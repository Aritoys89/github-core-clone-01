// app.ts — a one-process GitHub-compatible git forge.
//
// A single dependency-free Node server that speaks four surfaces over one
// in-memory store:
//   * git smart HTTP (protocol v2 and v0) at /<owner>/<repo>.git/...
//   * the REST v3 API under /api/v3/
//   * GraphQL at /api/graphql
//   * MCP (streamable HTTP, JSON-RPC) at /mcp
//
// State lives entirely in memory: repositories are created through REST and
// everything else (refs, objects, issues, pull requests) hangs off them.
// The forge has exactly one account — the viewer the bearer token belongs
// to — so any repository addressed under a different owner is a 404.

import { createServer } from 'node:http';
import type { IncomingMessage, Server, ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// Constants and small helpers
// ---------------------------------------------------------------------------

const VIEWER = {
  login: 'adaiversen',
  id: 1000,
  name: 'ada iversen',
  email: 'adaiversen@example.invalid',
  type: 'User',
};

const ZERO_OID = '0'.repeat(40);
const SERVER_AGENT = 'makefun-forge/1.0.0';
const FORGE_VERSION = '1.0.0';

// A logical clock keeps every timestamp the forge invents deterministic:
// it starts at MAKEFUN_TRIAL_NOW when the environment provides one and
// advances one second per use, so ordering by creation time always agrees
// with insertion order.
function openingSecond(): number {
  const raw = process.env.MAKEFUN_TRIAL_NOW;
  if (raw) {
    const asNumber = Number(raw);
    if (Number.isFinite(asNumber) && asNumber > 0) {
      return asNumber > 1e12 ? Math.floor(asNumber / 1000) : Math.floor(asNumber);
    }
    const parsed = Date.parse(raw);
    if (Number.isFinite(parsed)) return Math.floor(parsed / 1000);
  }
  return 1735689600; // 2025-01-01T00:00:00Z
}
let clockSecond = openingSecond();
function tick(): number {
  clockSecond += 1;
  return clockSecond;
}
// Formatting a second as ISO text is pure, and the logical clock hands
// the same second to many serializers in a row, so keep the last result.
let isoMemoSec = -1;
let isoMemoText = '';
function isoOf(sec: number): string {
  if (sec === isoMemoSec) return isoMemoText;
  const text = new Date(sec * 1000).toISOString();
  isoMemoSec = sec;
  isoMemoText = text;
  return text;
}

function b64Encode(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}
function b64Decode(text: string): string {
  return Buffer.from(text, 'base64').toString('utf8');
}
function isOid(text: unknown): text is string {
  return typeof text === 'string' && /^[0-9a-f]{40}$/.test(text);
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

interface GitObject {
  type: string; // 'blob' | 'tree' | 'commit' | 'tag'
  data: Buffer;
  packed?: Buffer; // cached deflated form, objects are immutable
}

interface CommentRec {
  id: number;
  body: string;
  createdSec: number;
  updatedSec: number;
}

interface IssueRec {
  number: number;
  gid: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: CommentRec[];
  createdSec: number;
  updatedSec: number;
  closedSec: number | null;
  // The last serialized single-issue response and the exact inputs it
  // was built from; sendIssueJson reuses the bytes only while every one
  // of those inputs still matches.
  getCache?: {
    host: string;
    updatedSec: number;
    commentCount: number;
    labels: string[];
    repoName: string;
    body: Buffer;
  };
}

interface PullRec {
  number: number;
  gid: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  merged: boolean;
  headRef: string;
  baseRef: string;
  comments: CommentRec[];
  createdSec: number;
  updatedSec: number;
  mergedSec: number | null;
  mergeSha: string | null;
}

interface LabelRec {
  id: number;
  name: string;
  color: string;
  description: string;
}

interface Repo {
  dbId: number;
  name: string;
  description: string;
  priv: boolean;
  defaultBranch: string;
  createdSec: number;
  updatedSec: number;
  objects: Map<string, GitObject>;
  refs: Map<string, string>; // full ref name -> oid
  labels: Map<string, LabelRec>;
  labelSeq: number;
  issues: Map<number, IssueRec>;
  pulls: Map<number, PullRec>;
  numberSeq: number; // issues and pull requests share one number sequence
  gidSeq: number;
  commentSeq: number;
  packCache: Map<string, { pack: Buffer; plan: FetchPlan }>;
}

const reposByName = new Map<string, Repo>();
let repoSeq = 700000;
let gidSeq = 900000;

function newRepo(name: string, description: string, priv: boolean): Repo {
  repoSeq += 1;
  const now = tick();
  return {
    dbId: repoSeq,
    name,
    description,
    priv,
    defaultBranch: 'main',
    createdSec: now,
    updatedSec: now,
    objects: new Map(),
    refs: new Map(),
    labels: new Map(),
    labelSeq: 0,
    issues: new Map(),
    pulls: new Map(),
    numberSeq: 0,
    gidSeq: 0,
    commentSeq: 0,
    packCache: new Map(),
  };
}

function findRepo(owner: string, name: string): Repo | null {
  if (owner !== VIEWER.login) return null;
  return reposByName.get(name) ?? null;
}

function touchRepo(repo: Repo): void {
  repo.updatedSec = tick();
  repo.packCache.clear();
}

// ---------------------------------------------------------------------------
// Git object primitives
// ---------------------------------------------------------------------------

// The object id of a would-be stored object: SHA-1 over the header and
// the payload, fed to the hash in two updates so hashing never has to
// copy the payload into a joined buffer first.
function objectId(type: string, data: Buffer): string {
  return createHash('sha1')
    .update(`${type} ${data.length}\0`, 'utf8')
    .update(data)
    .digest('hex');
}

function storeObject(repo: Repo, type: string, data: Buffer): string {
  return storeObjectWithId(repo, type, data, objectId(type, data));
}

// Store an object whose id the caller has already computed (a pack's
// index pass hashes every plain entry once; resolving must not hash the
// same bytes a second time to store them).
function storeObjectWithId(repo: Repo, type: string, data: Buffer, oid: string): string {
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}

function getObject(repo: Repo, oid: string): GitObject | null {
  return repo.objects.get(oid) ?? null;
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let pos = 0;
  while (pos < data.length) {
    const space = data.indexOf(0x20, pos);
    const mode = data.toString('utf8', pos, space);
    const nul = data.indexOf(0x00, space + 1);
    const name = data.toString('utf8', space + 1, nul);
    const oid = data.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, oid });
    pos = nul + 21;
  }
  return entries;
}

// Git orders tree entries by name, with directories sorting as if their
// name ended in '/'.
function treeSortKey(entry: TreeEntry): string {
  return entry.mode === '40000' || entry.mode === '040000'
    ? `${entry.name}/`
    : entry.name;
}

function buildTree(repo: Repo, entries: TreeEntry[]): string {
  const sorted = [...entries].sort((a, b) => {
    const ka = treeSortKey(a);
    const kb = treeSortKey(b);
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return storeObject(repo, 'tree', Buffer.concat(parts));
}

interface FlatEntry {
  mode: string;
  oid: string;
}

function flattenTree(
  repo: Repo,
  treeOid: string | null,
  prefix: string,
  out: Map<string, FlatEntry>,
): Map<string, FlatEntry> {
  if (!treeOid) return out;
  const obj = getObject(repo, treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const entry of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${entry.name}` : entry.name;
    if (entry.mode === '40000' || entry.mode === '040000') {
      flattenTree(repo, entry.oid, path, out);
    } else {
      out.set(path, { mode: entry.mode, oid: entry.oid });
    }
  }
  return out;
}

function treeFromFlat(repo: Repo, flat: Map<string, FlatEntry>): string {
  // Group paths by their first segment, recursing into subdirectories.
  const files: TreeEntry[] = [];
  const dirs = new Map<string, Map<string, FlatEntry>>();
  for (const [path, entry] of flat) {
    const slash = path.indexOf('/');
    if (slash === -1) {
      files.push({ mode: entry.mode, name: path, oid: entry.oid });
    } else {
      const head = path.slice(0, slash);
      const rest = path.slice(slash + 1);
      let bucket = dirs.get(head);
      if (!bucket) {
        bucket = new Map();
        dirs.set(head, bucket);
      }
      bucket.set(rest, entry);
    }
  }
  const entries: TreeEntry[] = [...files];
  for (const [name, bucket] of dirs) {
    entries.push({ mode: '40000', name, oid: treeFromFlat(repo, bucket) });
  }
  return buildTree(repo, entries);
}

interface CommitInfo {
  tree: string;
  parents: string[];
  message: string;
  authorName: string;
  authorEmail: string;
  timeSec: number;
}

function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = ZERO_OID;
  const parents: string[] = [];
  let authorName = '';
  let authorEmail = '';
  let timeSec = 0;
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) {
      const m = /^(.*?) <(.*?)> (\d+)/.exec(line.slice(7));
      if (m) {
        authorName = m[1];
        authorEmail = m[2];
        timeSec = Number(m[3]);
      }
    }
  }
  return { tree, parents, message, authorName, authorEmail, timeSec };
}

function forgeIdent(sec: number): string {
  return `${VIEWER.name} <${VIEWER.email}> ${sec} +0000`;
}

function buildCommit(
  repo: Repo,
  tree: string,
  parents: string[],
  message: string,
  sec: number,
): string {
  const ident = forgeIdent(sec);
  let head = `tree ${tree}\n`;
  for (const parent of parents) head += `parent ${parent}\n`;
  head += `author ${ident}\ncommitter ${ident}\n`;
  return storeObject(repo, 'commit', Buffer.from(`${head}\n${message}`, 'utf8'));
}

function parseTagTarget(data: Buffer): string | null {
  const text = data.toString('utf8');
  const m = /^object ([0-9a-f]{40})$/m.exec(text);
  return m ? m[1] : null;
}

// Follow tag objects until a non-tag object (or a missing one) is reached.
function peelToCommit(repo: Repo, oid: string): string | null {
  let current = oid;
  for (let hops = 0; hops < 32; hops += 1) {
    const obj = getObject(repo, current);
    if (!obj) return null;
    if (obj.type === 'commit') return current;
    if (obj.type === 'tag') {
      const target = parseTagTarget(obj.data);
      if (!target) return null;
      current = target;
      continue;
    }
    return null;
  }
  return null;
}

// Every object reachable from the given tips, following commits to their
// trees and parents, tags to their targets and trees to their entries.
// Commits in `shallowBoundary` are included with their trees but their
// parents are not followed: a client holding a shallow commit holds
// exactly that much of it.
function fullClosure(
  repo: Repo,
  tips: string[],
  shallowBoundary?: Set<string>,
): Set<string> {
  const seen = new Set<string>();
  const stack = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    const obj = getObject(repo, oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const commit = parseCommit(obj.data);
      stack.push(commit.tree);
      if (!shallowBoundary || !shallowBoundary.has(oid)) {
        stack.push(...commit.parents);
      }
    } else if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) {
        if (entry.mode !== '160000') stack.push(entry.oid);
      }
    } else if (obj.type === 'tag') {
      const target = parseTagTarget(obj.data);
      if (target) stack.push(target);
    }
  }
  return seen;
}

function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  const start = peelToCommit(repo, descendant);
  const goal = peelToCommit(repo, ancestor);
  if (!start || !goal) return false;
  if (start === goal) return true;
  const seen = new Set<string>();
  const stack = [start];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    for (const parent of parseCommit(obj.data).parents) {
      if (parent === goal) return true;
      stack.push(parent);
    }
  }
  return false;
}

function mergeBase(repo: Repo, a: string, b: string): string | null {
  const ca = peelToCommit(repo, a);
  const cb = peelToCommit(repo, b);
  if (!ca || !cb) return null;
  const ancestorsOf = (tip: string): Map<string, number> => {
    const dist = new Map<string, number>([[tip, 0]]);
    const queue = [tip];
    while (queue.length > 0) {
      const oid = queue.shift() as string;
      const obj = getObject(repo, oid);
      if (!obj || obj.type !== 'commit') continue;
      for (const parent of parseCommit(obj.data).parents) {
        if (!dist.has(parent)) {
          dist.set(parent, (dist.get(oid) as number) + 1);
          queue.push(parent);
        }
      }
    }
    return dist;
  };
  const da = ancestorsOf(ca);
  const db = ancestorsOf(cb);
  let best: string | null = null;
  let bestScore = Infinity;
  for (const [oid, distA] of da) {
    const distB = db.get(oid);
    if (distB !== undefined && distA + distB < bestScore) {
      bestScore = distA + distB;
      best = oid;
    }
  }
  return best;
}

// ---------------------------------------------------------------------------
// Tree merging and diffing (used by pull request merges and file lists)
// ---------------------------------------------------------------------------

// Three-way merge of two trees against their common ancestor's tree.
// Returns the merged tree oid, or null when both sides changed the same
// path in different ways.
function mergeTrees(
  repo: Repo,
  baseTree: string,
  ourTree: string,
  theirTree: string,
): string | null {
  const base = flattenTree(repo, baseTree, '', new Map());
  const ours = flattenTree(repo, ourTree, '', new Map());
  const theirs = flattenTree(repo, theirTree, '', new Map());
  const paths = new Set<string>([
    ...base.keys(),
    ...ours.keys(),
    ...theirs.keys(),
  ]);
  const merged = new Map<string, FlatEntry>();
  const same = (x?: FlatEntry, y?: FlatEntry): boolean =>
    x === undefined && y === undefined
      ? true
      : x !== undefined && y !== undefined && x.oid === y.oid && x.mode === y.mode;
  for (const path of paths) {
    const b = base.get(path);
    const o = ours.get(path);
    const t = theirs.get(path);
    if (same(o, t)) {
      if (o) merged.set(path, o);
    } else if (same(b, o)) {
      if (t) merged.set(path, t);
    } else if (same(b, t)) {
      if (o) merged.set(path, o);
    } else {
      return null;
    }
  }
  return treeFromFlat(repo, merged);
}

interface FileChange {
  filename: string;
  status: 'added' | 'modified' | 'removed';
  additions: number;
  deletions: number;
}

// Line-based diff counts: an LCS over the two files' lines. Files in this
// forge are small, so a straightforward dynamic program is plenty.
function lineDiffCounts(oldData: Buffer, newData: Buffer): { additions: number; deletions: number } {
  const oldLines = oldData.toString('utf8').split('\n');
  const newLines = newData.toString('utf8').split('\n');
  const n = oldLines.length;
  const m = newLines.length;
  let prev = new Uint32Array(m + 1);
  let curr = new Uint32Array(m + 1);
  for (let i = n - 1; i >= 0; i -= 1) {
    for (let j = m - 1; j >= 0; j -= 1) {
      curr[j] =
        oldLines[i] === newLines[j]
          ? prev[j + 1] + 1
          : Math.max(prev[j], curr[j + 1]);
    }
    [prev, curr] = [curr, prev];
    curr.fill(0);
  }
  const common = prev[0];
  return { additions: m - common, deletions: n - common };
}

function countLines(data: Buffer): number {
  if (data.length === 0) return 0;
  const text = data.toString('utf8');
  const lines = text.split('\n');
  return text.endsWith('\n') ? lines.length - 1 : lines.length;
}

function diffTrees(repo: Repo, fromTree: string, toTree: string): FileChange[] {
  const from = flattenTree(repo, fromTree, '', new Map());
  const to = flattenTree(repo, toTree, '', new Map());
  const paths = new Set<string>([...from.keys(), ...to.keys()]);
  const changes: FileChange[] = [];
  for (const path of [...paths].sort()) {
    const a = from.get(path);
    const b = to.get(path);
    if (a && !b) {
      const obj = getObject(repo, a.oid);
      changes.push({
        filename: path,
        status: 'removed',
        additions: 0,
        deletions: obj ? countLines(obj.data) : 0,
      });
    } else if (!a && b) {
      const obj = getObject(repo, b.oid);
      changes.push({
        filename: path,
        status: 'added',
        additions: obj ? countLines(obj.data) : 0,
        deletions: 0,
      });
    } else if (a && b && a.oid !== b.oid) {
      const oldObj = getObject(repo, a.oid);
      const newObj = getObject(repo, b.oid);
      const counts =
        oldObj && newObj
          ? lineDiffCounts(oldObj.data, newObj.data)
          : { additions: 0, deletions: 0 };
      changes.push({
        filename: path,
        status: 'modified',
        additions: counts.additions,
        deletions: counts.deletions,
      });
    }
  }
  return changes;
}

// ---------------------------------------------------------------------------
// Packfiles
// ---------------------------------------------------------------------------

const TYPE_CODES: Record<string, number> = {
  commit: 1,
  tree: 2,
  blob: 3,
  tag: 4,
};
const CODE_TYPES: Record<number, string> = {
  1: 'commit',
  2: 'tree',
  3: 'blob',
  4: 'tag',
};

function packEntryHeader(type: string, size: number): Buffer {
  const code = TYPE_CODES[type];
  const bytes: number[] = [];
  let first = (code << 4) | (size & 0x0f);
  size = Math.floor(size / 16);
  if (size > 0) first |= 0x80;
  bytes.push(first);
  while (size > 0) {
    let byte = size & 0x7f;
    size = Math.floor(size / 128);
    if (size > 0) byte |= 0x80;
    bytes.push(byte);
  }
  return Buffer.from(bytes);
}

function buildPack(repo: Repo, oids: string[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'utf8');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(oids.length, 8);
  parts.push(header);
  for (const oid of oids) {
    const obj = getObject(repo, oid);
    if (!obj) continue;
    parts.push(packEntryHeader(obj.type, obj.data.length));
    if (!obj.packed) obj.packed = deflateSync(obj.data);
    parts.push(obj.packed);
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

// Apply a git delta (copy/insert instructions) to a base object's bytes.
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let pos = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos];
      pos += 1;
      value |= (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if ((byte & 0x80) === 0) break;
    }
    return value;
  };
  readVarint(); // base size, not needed beyond parsing
  const resultSize = readVarint();
  const out: Buffer[] = [];
  let produced = 0;
  while (pos < delta.length) {
    const op = delta[pos];
    pos += 1;
    if (op & 0x80) {
      let offset = 0;
      let size = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) {
          offset |= delta[pos] << (8 * bit);
          pos += 1;
        }
      }
      for (let bit = 0; bit < 3; bit += 1) {
        if (op & (0x10 << bit)) {
          size |= delta[pos] << (8 * bit);
          pos += 1;
        }
      }
      if (size === 0) size = 0x10000;
      out.push(base.subarray(offset, offset + size));
      produced += size;
    } else if (op > 0) {
      out.push(delta.subarray(pos, pos + op));
      produced += op;
      pos += op;
    } else {
      throw new Error('delta opcode 0 is reserved');
    }
  }
  const result = Buffer.concat(out);
  if (result.length !== resultSize || produced !== resultSize) {
    throw new Error('delta result size mismatch');
  }
  return result;
}

// Inflate one zlib stream starting at `pos` inside a larger buffer and
// report how many compressed bytes it occupied. A zlib stream knows
// where it ends: asking for stream info makes the engine report exactly
// how many input bytes it consumed, so one inflate yields both the data
// and the offset of whatever follows the stream.
function inflateOne(buf: Buffer, pos: number): { data: Buffer; next: number } {
  let outcome: { buffer: Buffer; engine: { bytesWritten: number } };
  try {
    outcome = inflateSync(buf.subarray(pos), { info: true }) as unknown as {
      buffer: Buffer;
      engine: { bytesWritten: number };
    };
  } catch {
    throw new Error('corrupt zlib stream in pack');
  }
  const consumed = outcome.engine.bytesWritten;
  if (!Number.isInteger(consumed) || consumed <= 0) {
    throw new Error('corrupt zlib stream in pack');
  }
  return { data: outcome.buffer, next: pos + consumed };
}

interface PackEntry {
  type: string;
  data?: Buffer;
  delta?: Buffer;
  baseOid?: string;
  baseOffset?: number;
  entryStart: number;
  oid?: string; // a plain entry's id, computed by the index pass when one runs
}

// Read a pack into the repo's store; returns the oids it carried.
function readPack(repo: Repo, pack: Buffer): string[] {
  if (pack.length < 12 || pack.toString('utf8', 0, 4) !== 'PACK') {
    throw new Error('not a packfile');
  }
  const count = pack.readUInt32BE(8);
  let pos = 12;
  const entries: PackEntry[] = [];
  const byStart = new Map<number, number>();
  for (let i = 0; i < count; i += 1) {
    const entryStart = pos;
    let byte = pack[pos];
    pos += 1;
    const code = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[pos];
      pos += 1;
      size |= (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    void size;
    if (code === 6) {
      // OFS_DELTA: the base entry sits at a negative offset from this one.
      let b = pack[pos];
      pos += 1;
      let offset = b & 0x7f;
      while (b & 0x80) {
        b = pack[pos];
        pos += 1;
        offset = ((offset + 1) << 7) | (b & 0x7f);
      }
      const inflated = inflateOne(pack, pos);
      pos = inflated.next;
      entries.push({
        type: '',
        delta: inflated.data,
        baseOffset: entryStart - offset,
        entryStart,
      });
    } else if (code === 7) {
      // REF_DELTA: the base is named by oid, in this pack or the store.
      const baseOid = pack.toString('hex', pos, pos + 20);
      pos += 20;
      const inflated = inflateOne(pack, pos);
      pos = inflated.next;
      entries.push({ type: '', delta: inflated.data, baseOid, entryStart });
    } else {
      const type = CODE_TYPES[code];
      if (!type) throw new Error(`unknown pack object type ${code}`);
      const inflated = inflateOne(pack, pos);
      pos = inflated.next;
      entries.push({ type, data: inflated.data, entryStart });
    }
    byStart.set(entryStart, i);
  }
  // Index the plain entries by object id once, so a REF_DELTA base lookup
  // is a single map hit instead of a rescan that rehashes every candidate
  // entry for every delta in the pack. The index exists only for those
  // lookups: a pack carrying no REF_DELTA never consults it, so building
  // it there would hash every object for nothing. When the index does
  // run, each plain entry keeps the id it computed, and resolving stores
  // through it instead of hashing the same bytes again.
  const indexByOid = new Map<string, number>();
  if (entries.some((entry) => entry.baseOid !== undefined)) {
    entries.forEach((entry, index) => {
      if (entry.data !== undefined) {
        const oid = objectId(entry.type, entry.data);
        entry.oid = oid;
        indexByOid.set(oid, index);
      }
    });
  }
  // Resolve entries (deltas may chain) and store every object.
  const resolved: (string | null)[] = entries.map(() => null);
  const resolve = (index: number, depth: number): string => {
    const done = resolved[index];
    if (done) return done;
    if (depth > 64) throw new Error('delta chain too deep');
    const entry = entries[index];
    let oid: string;
    if (entry.data !== undefined) {
      oid =
        entry.oid !== undefined
          ? storeObjectWithId(repo, entry.type, entry.data, entry.oid)
          : storeObject(repo, entry.type, entry.data);
    } else {
      let baseType: string;
      let baseData: Buffer;
      if (entry.baseOid !== undefined) {
        const inPack = indexByOid.get(entry.baseOid) ?? -1;
        if (inPack >= 0) {
          const baseEntry = entries[inPack];
          baseType = baseEntry.type;
          baseData = baseEntry.data as Buffer;
          resolve(inPack, depth + 1);
        } else {
          const stored = getObject(repo, entry.baseOid);
          if (!stored) throw new Error('delta base is missing');
          baseType = stored.type;
          baseData = stored.data;
        }
      } else {
        const baseIndex = byStart.get(entry.baseOffset as number);
        if (baseIndex === undefined) throw new Error('delta base offset is invalid');
        oid = resolve(baseIndex, depth + 1);
        const stored = getObject(repo, oid);
        if (!stored) throw new Error('delta base is missing');
        baseType = stored.type;
        baseData = stored.data;
      }
      const data = applyDelta(baseData, entry.delta as Buffer);
      oid = storeObject(repo, baseType, data);
    }
    resolved[index] = oid;
    return oid;
  };
  const oids: string[] = [];
  for (let i = 0; i < entries.length; i += 1) oids.push(resolve(i, 0));
  return oids;
}

// ---------------------------------------------------------------------------
// Fetch object selection
// ---------------------------------------------------------------------------

interface FetchPlan {
  oids: string[]; // objects to put in the pack, in send order
  boundary: string[]; // commits to report as shallow in the reply
  unshallow: string[]; // client-shallow commits that are no longer boundary
}

// Choose the objects for a fetch: everything reachable from the wants that
// is not already reachable from the haves, honouring a depth limit counted
// in commit generations when one is given.
function planFetch(
  repo: Repo,
  wants: string[],
  haves: string[],
  depth: number | null,
  clientShallow: string[],
): FetchPlan {
  const haveSet = fullClosure(
    repo,
    haves.filter((oid) => getObject(repo, oid)),
    new Set(clientShallow),
  );
  const included = new Set<string>();
  const commitOrder: string[] = [];
  const boundary = new Set<string>();

  const includeTreeClosure = (treeOid: string): void => {
    const stack = [treeOid];
    while (stack.length > 0) {
      const oid = stack.pop() as string;
      if (included.has(oid) || haveSet.has(oid)) continue;
      const obj = getObject(repo, oid);
      if (!obj) continue;
      included.add(oid);
      if (obj.type === 'tree') {
        for (const entry of parseTree(obj.data)) {
          if (entry.mode !== '160000') stack.push(entry.oid);
        }
      }
    }
  };

  // Breadth-first over commits so depth counts generations. Traversal
  // descends through commits the client already has (a deepen starts from
  // a held boundary commit); only inclusion in the pack skips them.
  const distance = new Map<string, number>();
  const queue: string[] = [];
  const seed = (oid: string, dist: number): void => {
    const obj = getObject(repo, oid);
    if (!obj) return;
    if (obj.type === 'tag') {
      if (!haveSet.has(oid)) included.add(oid);
      const target = parseTagTarget(obj.data);
      if (target) seed(target, dist);
      return;
    }
    if (obj.type !== 'commit') {
      includeTreeClosure(oid);
      return;
    }
    if (distance.has(oid)) return;
    distance.set(oid, dist);
    queue.push(oid);
  };
  for (const want of wants) seed(want, 0);
  while (queue.length > 0) {
    const oid = queue.shift() as string;
    const dist = distance.get(oid) as number;
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    const commit = parseCommit(obj.data);
    if (!haveSet.has(oid)) {
      included.add(oid);
      commitOrder.push(oid);
      includeTreeClosure(commit.tree);
    }
    const atLimit = depth !== null && dist + 1 >= depth;
    if (atLimit) {
      if (commit.parents.length > 0 && !haveSet.has(oid)) boundary.add(oid);
    } else {
      for (const parent of commit.parents) {
        if (!distance.has(parent)) {
          distance.set(parent, dist + 1);
          queue.push(parent);
        }
      }
    }
  }

  const commitSet = new Set(commitOrder);
  const rest: string[] = [];
  for (const oid of included) {
    if (!commitSet.has(oid)) rest.push(oid);
  }
  const unshallow = clientShallow.filter(
    (oid) => distance.has(oid) && !boundary.has(oid),
  );
  return { oids: [...commitOrder, ...rest], boundary: [...boundary], unshallow };
}

function packForFetch(
  repo: Repo,
  wants: string[],
  haves: string[],
  depth: number | null,
  clientShallow: string[],
): { pack: Buffer; plan: FetchPlan } {
  const key = [
    'fetch',
    [...wants].sort().join(','),
    [...haves].sort().join(','),
    depth === null ? 'full' : String(depth),
    [...clientShallow].sort().join(','),
  ].join('|');
  // The plan is a pure function of the key's inputs and the store the key
  // was computed against, and touchRepo empties this cache on every
  // mutation, so a hit can hand back the plan alongside the pack instead
  // of walking the history again to rebuild an identical one. Callers
  // only read the plan's arrays, never mutate them.
  const cached = repo.packCache.get(key);
  if (cached) return cached;
  const plan = planFetch(repo, wants, haves, depth, clientShallow);
  const pack = buildPack(repo, plan.oids);
  const entry = { pack, plan };
  repo.packCache.set(key, entry);
  return entry;
}

// ---------------------------------------------------------------------------
// pkt-line framing
// ---------------------------------------------------------------------------

function pktLine(payload: Buffer | string): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  // Frame in a single allocation: 4 hex header bytes, then the payload
  // copied in once, instead of a header buffer joined by a concat.
  const framed = Buffer.allocUnsafe(body.length + 4);
  framed.write((body.length + 4).toString(16).padStart(4, '0'), 0, 'ascii');
  body.copy(framed, 4);
  return framed;
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
const PKT_RESPONSE_END = Buffer.from('0002', 'ascii');
void PKT_RESPONSE_END;

type PktToken = Buffer | 'flush' | 'delim' | 'response-end';

function decodePkts(buf: Buffer, start: number): { tokens: PktToken[]; end: number } {
  const tokens: PktToken[] = [];
  let pos = start;
  while (pos + 4 <= buf.length) {
    const header = buf.toString('ascii', pos, pos + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = parseInt(header, 16);
    if (length === 0) {
      tokens.push('flush');
      pos += 4;
      break;
    }
    if (length === 1) {
      tokens.push('delim');
      pos += 4;
      continue;
    }
    if (length === 2) {
      tokens.push('response-end');
      pos += 4;
      continue;
    }
    if (length < 4 || pos + length > buf.length) break;
    tokens.push(buf.subarray(pos + 4, pos + length));
    pos += length;
  }
  return { tokens, end: pos };
}

// Side-band framing: each packet's payload starts with a band byte.
function sidebandPackets(data: Buffer, band: number): Buffer[] {
  const packets: Buffer[] = [];
  // A pkt-line is at most 65520 bytes including its 4-byte header, and the
  // band byte rides inside the payload: 65520 - 4 - 1 bytes of data each.
  // Each packet is framed in one allocation (header, band byte, data)
  // rather than concatenating a band buffer and then framing the result.
  const maxPayload = 65515;
  for (let off = 0; off < data.length; off += maxPayload) {
    const chunk = data.subarray(off, off + maxPayload);
    const framed = Buffer.allocUnsafe(chunk.length + 5);
    framed.write((chunk.length + 5).toString(16).padStart(4, '0'), 0, 'ascii');
    framed[4] = band;
    chunk.copy(framed, 5);
    packets.push(framed);
  }
  if (packets.length === 0) {
    const framed = Buffer.allocUnsafe(5);
    framed.write('0005', 0, 'ascii');
    framed[4] = band;
    packets.push(framed);
  }
  return packets;
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

let requestSeq = 0;

// The timestamp half of a request id, memoized per millisecond: the
// clock is still read on every call, and a reading that differs from
// the last one is converted fresh, so the values handed out are exactly
// the ones an unmemoized conversion would produce.
let lastIdMs = -1;
let lastIdMs36 = '';

function requestId(): string {
  requestSeq += 1;
  const now = Date.now();
  if (now !== lastIdMs) {
    lastIdMs = now;
    lastIdMs36 = now.toString(36);
  }
  return `forge-${requestSeq.toString(36)}-${lastIdMs36}`;
}

function expectedToken(): string {
  return process.env.MAKEFUN_SHOP_TOKEN ?? '';
}

// The token is fixed for the life of the process (the harness sets it
// before startup), so resolve the full expected header once instead of
// re-reading the environment on every request. An empty string means no
// token is configured at all.
let expectedAuthHeader: string | null = null;

function authorized(req: IncomingMessage): boolean {
  if (expectedAuthHeader === null) {
    const token = expectedToken();
    expectedAuthHeader = token ? `Bearer ${token}` : '';
  }
  if (expectedAuthHeader === '') return true; // local development without a configured token
  return req.headers.authorization === expectedAuthHeader;
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > 268435456) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () =>
      resolve(chunks.length === 1 ? chunks[0] : Buffer.concat(chunks)),
    );
    req.on('error', reject);
  });
}

// Send an already-serialized JSON body with the standard response
// headers; sendJson is this plus the stringify step.
function sendJsonBuffer(
  res: ServerResponse,
  status: number,
  body: Buffer,
  extraHeaders: Record<string, string> = {},
): void {
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': String(body.length),
    'x-github-request-id': requestId(),
    ...extraHeaders,
  });
  res.end(body);
}

function sendJson(
  res: ServerResponse,
  status: number,
  value: unknown,
  extraHeaders: Record<string, string> = {},
): void {
  sendJsonBuffer(res, status, Buffer.from(JSON.stringify(value), 'utf8'), extraHeaders);
}

function sendEmpty(res: ServerResponse, status: number): void {
  res.writeHead(status, { 'x-github-request-id': requestId() });
  res.end();
}

function notFound(res: ServerResponse): void {
  sendJson(res, 404, { message: 'Not Found' });
}

function badCredentials(res: ServerResponse): void {
  sendJson(res, 401, { message: 'Bad credentials' });
}

// ---------------------------------------------------------------------------
// REST serializers
// ---------------------------------------------------------------------------

function hostOf(req: IncomingMessage): string {
  return req.headers.host ?? 'localhost';
}

function userJson(): Record<string, unknown> {
  return {
    login: VIEWER.login,
    id: VIEWER.id,
    node_id: b64Encode(`User:${VIEWER.id}`),
    type: VIEWER.type,
    site_admin: false,
    name: VIEWER.name,
    email: VIEWER.email,
  };
}

function repoJson(req: IncomingMessage, repo: Repo): Record<string, unknown> {
  const base = `http://${hostOf(req)}/api/v3/repos/${VIEWER.login}/${repo.name}`;
  return {
    id: repo.dbId,
    node_id: b64Encode(`Repository:${repo.dbId}`),
    name: repo.name,
    full_name: `${VIEWER.login}/${repo.name}`,
    owner: userJson(),
    private: repo.priv,
    html_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}`,
    description: repo.description,
    fork: false,
    url: base,
    created_at: isoOf(repo.createdSec),
    updated_at: isoOf(repo.updatedSec),
    pushed_at: isoOf(repo.updatedSec),
    git_url: `git://${hostOf(req)}/${VIEWER.login}/${repo.name}.git`,
    ssh_url: `git@${hostOf(req)}:${VIEWER.login}/${repo.name}.git`,
    clone_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}.git`,
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    language: null,
    has_issues: true,
    has_projects: true,
    has_downloads: true,
    has_wiki: true,
    has_pages: false,
    forks_count: 0,
    archived: false,
    disabled: false,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
    license: null,
    visibility: repo.priv ? 'private' : 'public',
    default_branch: repo.defaultBranch,
    permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
  };
}

function labelJson(label: LabelRec): Record<string, unknown> {
  return {
    id: label.id,
    node_id: b64Encode(`Label:${label.id}`),
    name: label.name,
    color: label.color,
    default: false,
    description: label.description,
  };
}

function issueJson(req: IncomingMessage, repo: Repo, issue: IssueRec): Record<string, unknown> {
  const base = `http://${hostOf(req)}/api/v3/repos/${VIEWER.login}/${repo.name}`;
  return {
    id: issue.gid,
    node_id: b64Encode(`Issue:${repo.dbId}:${issue.number}`),
    url: `${base}/issues/${issue.number}`,
    repository_url: base,
    html_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}/issues/${issue.number}`,
    number: issue.number,
    state: issue.state,
    title: issue.title,
    body: issue.body,
    user: userJson(),
    labels: issue.labels
      .map((name) => repo.labels.get(name))
      .filter((label): label is LabelRec => label !== undefined)
      .map(labelJson),
    assignee: null,
    assignees: [],
    comments: issue.comments.length,
    created_at: isoOf(issue.createdSec),
    updated_at: isoOf(issue.updatedSec),
    closed_at: issue.closedSec === null ? null : isoOf(issue.closedSec),
  };
}

// Answer a single-issue response, reusing the serialized bytes while
// every input the representation depends on still matches: the host the
// URLs are built for, the update stamp (every patch and every close
// moves it), the comment count (comments are append-only), the labels
// array itself (patches swap it wholesale, and label records are never
// edited after creation), and the repository's name. On any drift the
// body is rebuilt and the cache refreshed.
function sendIssueJson(
  req: IncomingMessage,
  res: ServerResponse,
  repo: Repo,
  issue: IssueRec,
  status = 200,
): void {
  const cache = issue.getCache;
  if (
    cache &&
    cache.host === hostOf(req) &&
    cache.updatedSec === issue.updatedSec &&
    cache.commentCount === issue.comments.length &&
    cache.labels === issue.labels &&
    cache.repoName === repo.name
  ) {
    sendJsonBuffer(res, status, cache.body);
    return;
  }
  const body = Buffer.from(JSON.stringify(issueJson(req, repo, issue)), 'utf8');
  issue.getCache = {
    host: hostOf(req),
    updatedSec: issue.updatedSec,
    commentCount: issue.comments.length,
    labels: issue.labels,
    repoName: repo.name,
    body,
  };
  sendJsonBuffer(res, status, body);
}

function commentJson(
  req: IncomingMessage,
  repo: Repo,
  issueNumber: number,
  comment: CommentRec,
): Record<string, unknown> {
  const base = `http://${hostOf(req)}/api/v3/repos/${VIEWER.login}/${repo.name}`;
  return {
    id: comment.id,
    node_id: b64Encode(`IssueComment:${comment.id}`),
    url: `${base}/issues/comments/${comment.id}`,
    html_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}/issues/${issueNumber}#issuecomment-${comment.id}`,
    body: comment.body,
    user: userJson(),
    created_at: isoOf(comment.createdSec),
    updated_at: isoOf(comment.updatedSec),
  };
}

// The outcome of trying to merge a pull request right now.
type MergeAttempt =
  | { ok: true; tree: string; baseTip: string }
  | { ok: false; reason: string };

function attemptMerge(repo: Repo, pull: PullRec): MergeAttempt {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`);
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  if (!headTip || !baseTip) return { ok: false, reason: 'a branch is missing' };
  const headCommit = peelToCommit(repo, headTip);
  const baseCommit = peelToCommit(repo, baseTip);
  if (!headCommit || !baseCommit) return { ok: false, reason: 'tip is not a commit' };
  if (headCommit === baseCommit) return { ok: false, reason: 'nothing to merge' };
  if (isAncestor(repo, headCommit, baseCommit)) {
    return { ok: false, reason: 'head is already contained in base' };
  }
  const base = mergeBase(repo, headCommit, baseCommit);
  if (!base) return { ok: false, reason: 'no common ancestor' };
  const baseObj = getObject(repo, base);
  const headObj = getObject(repo, headCommit);
  const baseTipObj = getObject(repo, baseCommit);
  if (!baseObj || !headObj || !baseTipObj) return { ok: false, reason: 'object missing' };
  const mergedTree = mergeTrees(
    repo,
    parseCommit(baseObj.data).tree,
    parseCommit(baseTipObj.data).tree,
    parseCommit(headObj.data).tree,
  );
  if (!mergedTree) return { ok: false, reason: 'merge conflict' };
  return { ok: true, tree: mergedTree, baseTip: baseCommit };
}

// Perform the squash merge: one new commit on the base branch whose tree
// is the three-way merge and whose only parent is the base tip.
function performMerge(repo: Repo, pull: PullRec): MergeAttempt & { sha?: string } {
  const attempt = attemptMerge(repo, pull);
  if (!attempt.ok) return attempt;
  const now = tick();
  const sha = buildCommit(
    repo,
    attempt.tree,
    [attempt.baseTip],
    `${pull.title} (#${pull.number})`,
    now,
  );
  repo.refs.set(`refs/heads/${pull.baseRef}`, sha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedSec = now;
  pull.mergeSha = sha;
  pull.updatedSec = now;
  touchRepo(repo);
  return { ...attempt, sha };
}

function pullJson(req: IncomingMessage, repo: Repo, pull: PullRec): Record<string, unknown> {
  const base = `http://${hostOf(req)}/api/v3/repos/${VIEWER.login}/${repo.name}`;
  const side = (ref: string): Record<string, unknown> => ({
    label: `${VIEWER.login}:${ref}`,
    ref,
    sha: repo.refs.get(`refs/heads/${ref}`) ?? null,
    user: userJson(),
    repo: repoJson(req, repo),
  });
  return {
    id: pull.gid,
    node_id: b64Encode(`PullRequest:${repo.dbId}:${pull.number}`),
    url: `${base}/pulls/${pull.number}`,
    html_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}/pull/${pull.number}`,
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    user: userJson(),
    head: side(pull.headRef),
    base: side(pull.baseRef),
    merged: pull.merged,
    merged_at: pull.mergedSec === null ? null : isoOf(pull.mergedSec),
    merge_commit_sha: pull.mergeSha,
    mergeable: pull.merged ? true : pull.state === 'open' ? attemptMerge(repo, pull).ok : null,
    comments: pull.comments.length,
    created_at: isoOf(pull.createdSec),
    updated_at: isoOf(pull.updatedSec),
    closed_at: pull.state === 'closed' ? isoOf(pull.updatedSec) : null,
  };
}

// ---------------------------------------------------------------------------
// REST v3 handlers
// ---------------------------------------------------------------------------

// The slice of a parsed request target the handlers actually read: the
// raw path and the decoded query parameters. A WHATWG URL satisfies this
// structurally, and the dispatcher also builds it directly from the raw
// target for the common shapes (see parseRequestTarget in createApp).
interface RequestUrl {
  pathname: string;
  searchParams: URLSearchParams;
}

interface RestContext {
  req: IncomingMessage;
  res: ServerResponse;
  url: RequestUrl;
  body: Record<string, unknown>;
}

function pageParams(url: RequestUrl): { page: number; perPage: number } {
  const page = Math.max(1, Number(url.searchParams.get('page') ?? '1') || 1);
  const perPage = Math.min(
    100,
    Math.max(1, Number(url.searchParams.get('per_page') ?? '30') || 30),
  );
  return { page, perPage };
}

function paginate<T>(ctx: RestContext, items: T[]): T[] {
  const { page, perPage } = pageParams(ctx.url);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  if (start + perPage < items.length) {
    // The Link URLs must stay on the origin the client actually used, so
    // they are rebuilt from the request's Host header, not from the
    // internal parse base.
    const build = (page: number): string => {
      const params = new URLSearchParams(ctx.url.searchParams);
      params.set('page', String(page));
      return `http://${hostOf(ctx.req)}${ctx.url.pathname}?${params.toString()}`;
    };
    ctx.res.setHeader(
      'Link',
      `<${build(page + 1)}>; rel="next", <${build(Math.ceil(items.length / perPage))}>; rel="last"`,
    );
  }
  return slice;
}

function validationFailed(res: ServerResponse, message: string): void {
  sendJson(res, 422, { message: `Validation Failed: ${message}` });
}

function restRoot(ctx: RestContext): void {
  const host = hostOf(ctx.req);
  sendJson(
    ctx.res,
    200,
    {
      current_user_url: `http://${host}/api/v3/user`,
      current_user_repositories_url: `http://${host}/api/v3/user/repos`,
      repository_url: `http://${host}/api/v3/repos/{owner}/{repo}`,
      issue_url: `http://${host}/api/v3/repos/{owner}/{repo}/issues`,
      emojis_url: `http://${host}/api/v3/emojis`,
      rate_limit_url: `http://${host}/api/v3/rate_limit`,
    },
    { 'x-oauth-scopes': 'repo, read:org' },
  );
}

function restCreateRepo(ctx: RestContext): void {
  const name = ctx.body.name;
  if (typeof name !== 'string' || name.length === 0) {
    validationFailed(ctx.res, 'name is required');
    return;
  }
  if (reposByName.has(name)) {
    sendJson(ctx.res, 422, {
      message: `Repository creation failed: a repository with that name '${name}' already exists on this account`,
    });
    return;
  }
  const repo = newRepo(
    name,
    typeof ctx.body.description === 'string' ? ctx.body.description : '',
    ctx.body.private === true,
  );
  reposByName.set(name, repo);
  sendJson(ctx.res, 201, repoJson(ctx.req, repo));
}

function restListUserRepos(ctx: RestContext): void {
  const all = [...reposByName.values()].sort((a, b) => a.dbId - b.dbId);
  sendJson(ctx.res, 200, paginate(ctx, all).map((repo) => repoJson(ctx.req, repo)));
}

// Resolve a ref-ish string (branch, tag or oid) to a commit oid.
function resolveCommit(repo: Repo, ref: string | null | undefined): string | null {
  if (!ref) {
    const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    return tip ? peelToCommit(repo, tip) : null;
  }
  const branch = repo.refs.get(`refs/heads/${ref}`);
  if (branch) return peelToCommit(repo, branch);
  const tag = repo.refs.get(`refs/tags/${ref}`);
  if (tag) return peelToCommit(repo, tag);
  const anyRef = repo.refs.get(ref);
  if (anyRef) return peelToCommit(repo, anyRef);
  if (isOid(ref) && getObject(repo, ref)) return peelToCommit(repo, ref);
  return null;
}

function commitJsonFull(
  req: IncomingMessage,
  repo: Repo,
  sha: string,
): Record<string, unknown> {
  const obj = getObject(repo, sha);
  const commit = obj ? parseCommit(obj.data) : null;
  const base = `http://${hostOf(req)}/api/v3/repos/${VIEWER.login}/${repo.name}`;
  const ident = (name: string, email: string, sec: number) => ({
    name,
    email,
    date: isoOf(sec),
  });
  return {
    sha,
    node_id: b64Encode(`Commit:${sha}`),
    url: `${base}/commits/${sha}`,
    html_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}/commit/${sha}`,
    commit: {
      author: commit ? ident(commit.authorName, commit.authorEmail, commit.timeSec) : ident('', '', 0),
      committer: commit ? ident(commit.authorName, commit.authorEmail, commit.timeSec) : ident('', '', 0),
      message: commit ? commit.message : '',
      tree: { sha: commit ? commit.tree : ZERO_OID, url: `${base}/git/trees/${commit ? commit.tree : ZERO_OID}` },
      comment_count: 0,
    },
    author: userJson(),
    committer: userJson(),
    parents: (commit ? commit.parents : []).map((parent) => ({
      sha: parent,
      url: `${base}/commits/${parent}`,
      html_url: `http://${hostOf(req)}/${VIEWER.login}/${repo.name}/commit/${parent}`,
    })),
  };
}

function restListCommits(ctx: RestContext, repo: Repo): void {
  const shaParam = ctx.url.searchParams.get('sha');
  const start = resolveCommit(repo, shaParam);
  if (!start) {
    if (shaParam) {
      notFound(ctx.res);
      return;
    }
    sendJson(ctx.res, 200, []);
    return;
  }
  const ordered: string[] = [];
  const seen = new Set<string>();
  const visit = (oid: string): void => {
    if (seen.has(oid)) return;
    const obj = getObject(repo, oid);
    if (!obj || obj.type !== 'commit') return;
    seen.add(oid);
    ordered.push(oid);
    for (const parent of parseCommit(obj.data).parents) visit(parent);
  };
  visit(start);
  sendJson(ctx.res, 200, paginate(ctx, ordered).map((sha) => commitJsonFull(ctx.req, repo, sha)));
}

function restListBranches(ctx: RestContext, repo: Repo): void {
  const host = hostOf(ctx.req);
  const branches: Record<string, unknown>[] = [];
  for (const [ref, oid] of repo.refs) {
    if (!ref.startsWith('refs/heads/')) continue;
    branches.push({
      name: ref.slice('refs/heads/'.length),
      commit: {
        sha: oid,
        url: `http://${host}/api/v3/repos/${VIEWER.login}/${repo.name}/commits/${oid}`,
      },
      protected: false,
    });
  }
  branches.sort((a, b) => String(a.name).localeCompare(String(b.name)));
  sendJson(ctx.res, 200, branches);
}

function restGetBranch(ctx: RestContext, repo: Repo, name: string): void {
  const oid = repo.refs.get(`refs/heads/${name}`);
  if (!oid) {
    notFound(ctx.res);
    return;
  }
  const host = hostOf(ctx.req);
  sendJson(ctx.res, 200, {
    name,
    commit: {
      sha: oid,
      url: `http://${host}/api/v3/repos/${VIEWER.login}/${repo.name}/commits/${oid}`,
    },
    protected: false,
  });
}

function restCreateRef(ctx: RestContext, repo: Repo): void {
  const ref = ctx.body.ref;
  const sha = ctx.body.sha;
  if (typeof ref !== 'string' || !ref.startsWith('refs/') || !isOid(sha as string)) {
    validationFailed(ctx.res, 'ref and a valid sha are required');
    return;
  }
  if (!getObject(repo, sha as string)) {
    validationFailed(ctx.res, 'the sha does not name a known object');
    return;
  }
  if (repo.refs.has(ref)) {
    validationFailed(ctx.res, 'reference already exists');
    return;
  }
  repo.refs.set(ref, sha as string);
  touchRepo(repo);
  const obj = getObject(repo, sha as string);
  sendJson(ctx.res, 201, {
    ref,
    node_id: b64Encode(`Ref:${repo.dbId}:${ref}`),
    url: `http://${hostOf(ctx.req)}/api/v3/repos/${VIEWER.login}/${repo.name}/git/${ref}`,
    object: { type: obj ? obj.type : 'commit', sha, url: '' },
  });
}

function restGetRef(ctx: RestContext, repo: Repo, rest: string): void {
  const full = rest.startsWith('refs/') ? rest : `refs/${rest}`;
  const oid = repo.refs.get(full);
  if (!oid) {
    notFound(ctx.res);
    return;
  }
  const obj = getObject(repo, oid);
  sendJson(ctx.res, 200, {
    ref: full,
    node_id: b64Encode(`Ref:${repo.dbId}:${full}`),
    url: `http://${hostOf(ctx.req)}/api/v3/repos/${VIEWER.login}/${repo.name}/git/${full}`,
    object: { type: obj ? obj.type : 'commit', sha: oid, url: '' },
  });
}

// --- contents -------------------------------------------------------------

interface TreeLookup {
  kind: 'file' | 'dir';
  oid: string;
  mode: string;
}

function lookupPath(repo: Repo, treeOid: string, path: string): TreeLookup | null {
  if (path === '') return { kind: 'dir', oid: treeOid, mode: '40000' };
  const parts = path.split('/');
  let current = treeOid;
  for (let i = 0; i < parts.length; i += 1) {
    const obj = getObject(repo, current);
    if (!obj || obj.type !== 'tree') return null;
    const entry = parseTree(obj.data).find((e) => e.name === parts[i]);
    if (!entry) return null;
    if (i === parts.length - 1) {
      const isDir = entry.mode === '40000' || entry.mode === '040000';
      return { kind: isDir ? 'dir' : 'file', oid: entry.oid, mode: entry.mode };
    }
    if (!(entry.mode === '40000' || entry.mode === '040000')) return null;
    current = entry.oid;
  }
  return null;
}

function contentsCommitJson(
  req: IncomingMessage,
  repo: Repo,
  sha: string,
): Record<string, unknown> {
  const full = commitJsonFull(req, repo, sha);
  const commit = full.commit as Record<string, unknown>;
  return {
    sha,
    node_id: full.node_id,
    url: full.url,
    html_url: full.html_url,
    author: commit.author,
    committer: commit.committer,
    tree: commit.tree,
    message: commit.message,
    parents: full.parents,
  };
}

function restGetContents(ctx: RestContext, repo: Repo, path: string): void {
  const commit = resolveCommit(repo, ctx.url.searchParams.get('ref'));
  if (!commit) {
    notFound(ctx.res);
    return;
  }
  const commitObj = getObject(repo, commit);
  if (!commitObj) {
    notFound(ctx.res);
    return;
  }
  const treeOid = parseCommit(commitObj.data).tree;
  const found = lookupPath(repo, treeOid, path);
  if (!found) {
    notFound(ctx.res);
    return;
  }
  const host = hostOf(ctx.req);
  const base = `http://${host}/api/v3/repos/${VIEWER.login}/${repo.name}/contents`;
  if (found.kind === 'file') {
    const obj = getObject(repo, found.oid);
    if (!obj) {
      notFound(ctx.res);
      return;
    }
    const name = path.split('/').pop() ?? path;
    sendJson(ctx.res, 200, {
      type: 'file',
      encoding: 'base64',
      size: obj.data.length,
      name,
      path,
      content: obj.data.toString('base64').replace(/.{60}(?=.)/g, '$&\n'),
      sha: found.oid,
      url: `${base}/${path}`,
      html_url: `http://${host}/${VIEWER.login}/${repo.name}/blob/${repo.defaultBranch}/${path}`,
      download_url: `http://${host}/${VIEWER.login}/${repo.name}/raw/${repo.defaultBranch}/${path}`,
    });
    return;
  }
  const dirObj = getObject(repo, found.oid);
  if (!dirObj || dirObj.type !== 'tree') {
    notFound(ctx.res);
    return;
  }
  const entries = parseTree(dirObj.data).map((entry) => {
    const isDir = entry.mode === '40000' || entry.mode === '040000';
    const childPath = path ? `${path}/${entry.name}` : entry.name;
    const child = isDir ? null : getObject(repo, entry.oid);
    return {
      type: isDir ? 'dir' : 'file',
      size: child ? child.data.length : 0,
      name: entry.name,
      path: childPath,
      sha: entry.oid,
      url: `${base}/${childPath}`,
      html_url: `http://${host}/${VIEWER.login}/${repo.name}/blob/${repo.defaultBranch}/${childPath}`,
      download_url: isDir
        ? null
        : `http://${host}/${VIEWER.login}/${repo.name}/raw/${repo.defaultBranch}/${childPath}`,
    };
  });
  sendJson(ctx.res, 200, entries);
}

function restPutContents(ctx: RestContext, repo: Repo, path: string): void {
  const message = typeof ctx.body.message === 'string' ? ctx.body.message : '';
  const contentB64 = typeof ctx.body.content === 'string' ? ctx.body.content : '';
  const branch =
    typeof ctx.body.branch === 'string' && ctx.body.branch
      ? ctx.body.branch
      : repo.defaultBranch;
  const refName = `refs/heads/${branch}`;
  const tip = repo.refs.get(refName);
  const tipCommit = tip ? peelToCommit(repo, tip) : null;
  const flat = new Map<string, FlatEntry>();
  if (tipCommit) {
    const obj = getObject(repo, tipCommit);
    if (obj) flattenTree(repo, parseCommit(obj.data).tree, '', flat);
  }
  const existing = flat.get(path);
  const givenSha = typeof ctx.body.sha === 'string' ? ctx.body.sha : undefined;
  if (existing) {
    if (givenSha !== existing.oid) {
      sendJson(ctx.res, 409, {
        message: 'The sha provided does not match the current blob sha',
      });
      return;
    }
  } else if (givenSha !== undefined) {
    sendJson(ctx.res, 409, {
      message: 'The sha provided does not match the current blob sha',
    });
    return;
  }
  const data = Buffer.from(contentB64.replace(/\s+/g, ''), 'base64');
  const blobOid = storeObject(repo, 'blob', data);
  flat.set(path, { mode: '100644', oid: blobOid });
  const tree = treeFromFlat(repo, flat);
  const now = tick();
  const commit = buildCommit(repo, tree, tipCommit ? [tipCommit] : [], message, now);
  repo.refs.set(refName, commit);
  touchRepo(repo);
  const name = path.split('/').pop() ?? path;
  sendJson(ctx.res, existing ? 200 : 201, {
    content: {
      type: 'file',
      encoding: 'base64',
      size: data.length,
      name,
      path,
      sha: blobOid,
      url: `http://${hostOf(ctx.req)}/api/v3/repos/${VIEWER.login}/${repo.name}/contents/${path}`,
    },
    commit: contentsCommitJson(ctx.req, repo, commit),
  });
}

function restDeleteContents(ctx: RestContext, repo: Repo, path: string): void {
  const message = typeof ctx.body.message === 'string' ? ctx.body.message : '';
  const branch =
    typeof ctx.body.branch === 'string' && ctx.body.branch
      ? ctx.body.branch
      : repo.defaultBranch;
  const refName = `refs/heads/${branch}`;
  const tip = repo.refs.get(refName);
  const tipCommit = tip ? peelToCommit(repo, tip) : null;
  if (!tipCommit) {
    notFound(ctx.res);
    return;
  }
  const obj = getObject(repo, tipCommit);
  if (!obj) {
    notFound(ctx.res);
    return;
  }
  const flat = flattenTree(repo, parseCommit(obj.data).tree, '', new Map());
  const existing = flat.get(path);
  if (!existing) {
    notFound(ctx.res);
    return;
  }
  const givenSha = typeof ctx.body.sha === 'string' ? ctx.body.sha : undefined;
  if (givenSha !== existing.oid) {
    sendJson(ctx.res, 409, {
      message: 'The sha provided does not match the current blob sha',
    });
    return;
  }
  flat.delete(path);
  const tree = treeFromFlat(repo, flat);
  const commit = buildCommit(repo, tree, [tipCommit], message, tick());
  repo.refs.set(refName, commit);
  touchRepo(repo);
  sendJson(ctx.res, 200, {
    content: null,
    commit: contentsCommitJson(ctx.req, repo, commit),
  });
}

// --- labels, issues, comments, pulls --------------------------------------

function restCreateLabel(ctx: RestContext, repo: Repo): void {
  const name = ctx.body.name;
  if (typeof name !== 'string' || !name) {
    validationFailed(ctx.res, 'name is required');
    return;
  }
  if (repo.labels.has(name)) {
    validationFailed(ctx.res, 'name has already been taken');
    return;
  }
  repo.labelSeq += 1;
  const rawColor = typeof ctx.body.color === 'string' ? ctx.body.color : 'ededed';
  const label: LabelRec = {
    id: repo.labelSeq,
    name,
    color: rawColor.replace(/^#/, ''),
    description: typeof ctx.body.description === 'string' ? ctx.body.description : '',
  };
  repo.labels.set(name, label);
  sendJson(ctx.res, 201, labelJson(label));
}

function labelNamesOf(repo: Repo, raw: unknown): string[] | null {
  if (!Array.isArray(raw)) return [];
  const names: string[] = [];
  for (const item of raw) {
    const name =
      typeof item === 'string'
        ? item
        : item && typeof item === 'object' && typeof (item as { name?: unknown }).name === 'string'
          ? ((item as { name: string }).name as string)
          : null;
    if (name === null || !repo.labels.has(name)) return null;
    names.push(name);
  }
  return names;
}

function restCreateIssue(ctx: RestContext, repo: Repo): void {
  const title = ctx.body.title;
  if (typeof title !== 'string' || !title) {
    validationFailed(ctx.res, 'title is required');
    return;
  }
  const labels = labelNamesOf(repo, ctx.body.labels);
  if (labels === null) {
    validationFailed(ctx.res, 'one of the labels does not exist on this repository');
    return;
  }
  repo.numberSeq += 1;
  gidSeq += 1;
  const now = tick();
  const issue: IssueRec = {
    number: repo.numberSeq,
    gid: gidSeq,
    title,
    body: typeof ctx.body.body === 'string' ? ctx.body.body : '',
    state: 'open',
    labels,
    comments: [],
    createdSec: now,
    updatedSec: now,
    closedSec: null,
  };
  repo.issues.set(issue.number, issue);
  touchRepo(repo);
  sendIssueJson(ctx.req, ctx.res, repo, issue, 201);
}

function restListIssues(ctx: RestContext, repo: Repo): void {
  const stateParam = ctx.url.searchParams.get('state') ?? 'open';
  const direction = ctx.url.searchParams.get('direction') ?? 'desc';
  let issues = [...repo.issues.values()];
  if (stateParam === 'open') issues = issues.filter((i) => i.state === 'open');
  else if (stateParam === 'closed') issues = issues.filter((i) => i.state === 'closed');
  issues.sort((a, b) =>
    direction === 'asc'
      ? a.createdSec - b.createdSec || a.number - b.number
      : b.createdSec - a.createdSec || b.number - a.number,
  );
  sendJson(ctx.res, 200, paginate(ctx, issues).map((i) => issueJson(ctx.req, repo, i)));
}

function restPatchIssue(ctx: RestContext, repo: Repo, issue: IssueRec): void {
  if (typeof ctx.body.title === 'string') issue.title = ctx.body.title;
  if (typeof ctx.body.body === 'string') issue.body = ctx.body.body;
  if (ctx.body.labels !== undefined) {
    const labels = labelNamesOf(repo, ctx.body.labels);
    if (labels === null) {
      validationFailed(ctx.res, 'one of the labels does not exist on this repository');
      return;
    }
    issue.labels = labels;
  }
  if (ctx.body.state === 'closed' || ctx.body.state === 'open') {
    issue.state = ctx.body.state;
    issue.closedSec = ctx.body.state === 'closed' ? tick() : null;
  }
  issue.updatedSec = tick();
  sendIssueJson(ctx.req, ctx.res, repo, issue);
}

function commentTarget(repo: Repo, number: number): IssueRec | PullRec | null {
  return repo.issues.get(number) ?? repo.pulls.get(number) ?? null;
}

function restCreateComment(
  ctx: RestContext,
  repo: Repo,
  target: IssueRec | PullRec,
): void {
  const body = ctx.body.body;
  if (typeof body !== 'string') {
    validationFailed(ctx.res, 'body is required');
    return;
  }
  repo.commentSeq += 1;
  const now = tick();
  const comment: CommentRec = {
    id: repo.commentSeq,
    body,
    createdSec: now,
    updatedSec: now,
  };
  target.comments.push(comment);
  sendJson(ctx.res, 201, commentJson(ctx.req, repo, target.number, comment));
}

function stripOwnerPrefix(ref: string): string {
  const colon = ref.indexOf(':');
  return colon === -1 ? ref : ref.slice(colon + 1);
}

function restCreatePull(ctx: RestContext, repo: Repo): void {
  const head = typeof ctx.body.head === 'string' ? stripOwnerPrefix(ctx.body.head) : '';
  const base = typeof ctx.body.base === 'string' ? stripOwnerPrefix(ctx.body.base) : '';
  const title = typeof ctx.body.title === 'string' ? ctx.body.title : '';
  if (!head || !base || !repo.refs.has(`refs/heads/${head}`) || !repo.refs.has(`refs/heads/${base}`)) {
    validationFailed(ctx.res, 'head and base must name existing branches');
    return;
  }
  for (const pull of repo.pulls.values()) {
    if (pull.state === 'open' && pull.headRef === head && pull.baseRef === base) {
      validationFailed(ctx.res, `a pull request already exists for ${head} into ${base}`);
      return;
    }
  }
  repo.numberSeq += 1;
  gidSeq += 1;
  const now = tick();
  const pull: PullRec = {
    number: repo.numberSeq,
    gid: gidSeq,
    title,
    body: typeof ctx.body.body === 'string' ? ctx.body.body : '',
    state: 'open',
    merged: false,
    headRef: head,
    baseRef: base,
    comments: [],
    createdSec: now,
    updatedSec: now,
    mergedSec: null,
    mergeSha: null,
  };
  repo.pulls.set(pull.number, pull);
  touchRepo(repo);
  sendJson(ctx.res, 201, pullJson(ctx.req, repo, pull));
}

function restListPulls(ctx: RestContext, repo: Repo): void {
  const stateParam = ctx.url.searchParams.get('state') ?? 'open';
  let pulls = [...repo.pulls.values()];
  if (stateParam === 'open') pulls = pulls.filter((p) => p.state === 'open');
  else if (stateParam === 'closed') pulls = pulls.filter((p) => p.state === 'closed');
  pulls.sort((a, b) => b.createdSec - a.createdSec || b.number - a.number);
  sendJson(ctx.res, 200, paginate(ctx, pulls).map((p) => pullJson(ctx.req, repo, p)));
}

function restPullFiles(ctx: RestContext, repo: Repo, pull: PullRec): void {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`);
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  if (!headTip || !baseTip) {
    sendJson(ctx.res, 200, []);
    return;
  }
  const base = mergeBase(repo, headTip, baseTip) ?? peelToCommit(repo, baseTip);
  const headCommit = peelToCommit(repo, headTip);
  if (!base || !headCommit) {
    sendJson(ctx.res, 200, []);
    return;
  }
  const baseObj = getObject(repo, base);
  const headObj = getObject(repo, headCommit);
  if (!baseObj || !headObj) {
    sendJson(ctx.res, 200, []);
    return;
  }
  const changes = diffTrees(
    repo,
    parseCommit(baseObj.data).tree,
    parseCommit(headObj.data).tree,
  );
  const flatHead = flattenTree(repo, parseCommit(headObj.data).tree, '', new Map());
  const flatBase = flattenTree(repo, parseCommit(baseObj.data).tree, '', new Map());
  sendJson(
    ctx.res,
    200,
    changes.map((change) => ({
      sha: (flatHead.get(change.filename) ?? flatBase.get(change.filename))?.oid ?? ZERO_OID,
      filename: change.filename,
      status: change.status,
      additions: change.additions,
      deletions: change.deletions,
      changes: change.additions + change.deletions,
    })),
  );
}

function restMergePull(ctx: RestContext, repo: Repo, pull: PullRec): void {
  if (pull.merged) {
    sendJson(ctx.res, 405, { message: 'Pull Request was already merged' });
    return;
  }
  if (pull.state !== 'open') {
    sendJson(ctx.res, 405, { message: 'Pull Request is not open' });
    return;
  }
  const result = performMerge(repo, pull);
  if (!result.ok || !result.sha) {
    sendJson(ctx.res, 405, {
      message: `Pull Request is not mergeable: ${result.reason}`,
    });
    return;
  }
  sendJson(ctx.res, 200, {
    sha: result.sha,
    merged: true,
    message: 'Pull Request successfully merged',
  });
}

// --- REST dispatcher --------------------------------------------------------

// Synchronous by design: no step in REST dispatch or in any handler it
// routes to ever awaits, so declaring this async would only wrap every
// request's work in a promise nobody needs.
function handleRest(
  req: IncomingMessage,
  res: ServerResponse,
  segments: string[],
  url: RequestUrl,
  rawBody: Buffer,
): void {
  // segments[0..1] are 'api' and 'v3'; the rest routes from there.
  const parts = segments.slice(2);
  let body: Record<string, unknown> = {};
  if (rawBody.length > 0) {
    try {
      const parsed: unknown = JSON.parse(rawBody.toString('utf8'));
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
        body = parsed as Record<string, unknown>;
      }
    } catch {
      sendJson(res, 400, { message: 'Problems parsing JSON' });
      return;
    }
  }
  const ctx: RestContext = { req, res, url, body };
  const method = req.method ?? 'GET';

  if (!authorized(req)) {
    badCredentials(res);
    return;
  }
  if (parts.length === 0) {
    if (method === 'GET') return restRoot(ctx);
    return notFound(res);
  }
  if (parts[0] === 'meta' && parts.length === 1) {
    if (method === 'GET') {
      return sendJson(res, 200, {
        verifiable_password_authentication: false,
        installed_version: FORGE_VERSION,
      });
    }
    return notFound(res);
  }
  if (parts[0] === 'user' && parts.length === 1) {
    if (method === 'GET') return sendJson(res, 200, userJson());
    return notFound(res);
  }
  if (parts[0] === 'user' && parts[1] === 'repos' && parts.length === 2) {
    if (method === 'GET') return restListUserRepos(ctx);
    if (method === 'POST') return restCreateRepo(ctx);
    return notFound(res);
  }
  if (parts[0] !== 'repos' || parts.length < 3) return notFound(res);
  const repo = findRepo(parts[1], parts[2]);
  if (!repo) return notFound(res);
  const tail = parts.slice(3);

  if (tail.length === 0) {
    if (method === 'GET') return sendJson(res, 200, repoJson(req, repo));
    if (method === 'PATCH') {
      if (typeof body.description === 'string') repo.description = body.description;
      if (typeof body.private === 'boolean') repo.priv = body.private;
      if (typeof body.name === 'string' && body.name && body.name !== repo.name) {
        if (reposByName.has(body.name)) {
          return validationFailed(res, 'name has already been taken');
        }
        reposByName.delete(repo.name);
        repo.name = body.name;
        reposByName.set(repo.name, repo);
      }
      touchRepo(repo);
      return sendJson(res, 200, repoJson(req, repo));
    }
    if (method === 'DELETE') {
      reposByName.delete(repo.name);
      return sendEmpty(res, 204);
    }
    return notFound(res);
  }

  const [head, ...rest] = tail;
  if (head === 'branches') {
    if (rest.length === 0 && method === 'GET') return restListBranches(ctx, repo);
    if (rest.length >= 1 && method === 'GET') return restGetBranch(ctx, repo, rest.join('/'));
    return notFound(res);
  }
  if (head === 'commits') {
    if (rest.length === 0 && method === 'GET') return restListCommits(ctx, repo);
    if (rest.length === 1 && method === 'GET' && isOid(rest[0])) {
      if (!getObject(repo, rest[0])) return notFound(res);
      return sendJson(res, 200, commitJsonFull(req, repo, rest[0]));
    }
    return notFound(res);
  }
  if (head === 'git' && rest[0] === 'refs') {
    if (rest.length === 1 && method === 'POST') return restCreateRef(ctx, repo);
    if (rest.length === 1 && method === 'GET') {
      const list = [...repo.refs.entries()].map(([ref, oid]) => ({
        ref,
        node_id: b64Encode(`Ref:${repo.dbId}:${ref}`),
        object: { type: getObject(repo, oid)?.type ?? 'commit', sha: oid, url: '' },
      }));
      return sendJson(res, 200, list);
    }
    if (rest.length >= 2 && method === 'GET') return restGetRef(ctx, repo, rest.slice(1).join('/'));
    if (rest.length >= 2 && method === 'DELETE') {
      const full = `refs/${rest.slice(1).join('/')}`;
      if (!repo.refs.delete(full)) return notFound(res);
      touchRepo(repo);
      return sendEmpty(res, 204);
    }
    return notFound(res);
  }
  if (head === 'contents') {
    const path = rest.join('/');
    if (method === 'GET') return restGetContents(ctx, repo, path);
    if (method === 'PUT') return restPutContents(ctx, repo, path);
    if (method === 'DELETE') return restDeleteContents(ctx, repo, path);
    return notFound(res);
  }
  if (head === 'labels') {
    if (rest.length === 0 && method === 'GET') {
      return sendJson(res, 200, [...repo.labels.values()].map(labelJson));
    }
    if (rest.length === 0 && method === 'POST') return restCreateLabel(ctx, repo);
    if (rest.length === 1 && method === 'GET') {
      const label = repo.labels.get(rest[0]);
      if (!label) return notFound(res);
      return sendJson(res, 200, labelJson(label));
    }
    return notFound(res);
  }
  if (head === 'issues') {
    if (rest.length === 0 && method === 'GET') return restListIssues(ctx, repo);
    if (rest.length === 0 && method === 'POST') return restCreateIssue(ctx, repo);
    const number = Number(rest[0]);
    if (!Number.isInteger(number)) return notFound(res);
    if (rest.length === 1) {
      const issue = repo.issues.get(number);
      if (!issue) return notFound(res);
      if (method === 'GET') return sendIssueJson(req, res, repo, issue);
      if (method === 'PATCH') return restPatchIssue(ctx, repo, issue);
      return notFound(res);
    }
    if (rest.length === 2 && rest[1] === 'comments') {
      const target = commentTarget(repo, number);
      if (!target) return notFound(res);
      if (method === 'GET') {
        return sendJson(
          res,
          200,
          target.comments.map((c) => commentJson(req, repo, number, c)),
        );
      }
      if (method === 'POST') return restCreateComment(ctx, repo, target);
      return notFound(res);
    }
    return notFound(res);
  }
  if (head === 'pulls') {
    if (rest.length === 0 && method === 'GET') return restListPulls(ctx, repo);
    if (rest.length === 0 && method === 'POST') return restCreatePull(ctx, repo);
    const number = Number(rest[0]);
    if (!Number.isInteger(number)) return notFound(res);
    const pull = repo.pulls.get(number);
    if (!pull) return notFound(res);
    if (rest.length === 1 && method === 'GET') {
      return sendJson(res, 200, pullJson(req, repo, pull));
    }
    if (rest.length === 2 && rest[1] === 'files' && method === 'GET') {
      return restPullFiles(ctx, repo, pull);
    }
    if (rest.length === 2 && rest[1] === 'merge' && method === 'PUT') {
      return restMergePull(ctx, repo, pull);
    }
    return notFound(res);
  }
  return notFound(res);
}

// ---------------------------------------------------------------------------
// Git smart HTTP
// ---------------------------------------------------------------------------

function sortedRefs(repo: Repo): [string, string][] {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
}

function headTarget(repo: Repo): string {
  return `refs/heads/${repo.defaultBranch}`;
}

function advertisementV0(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps =
    service === 'git-upload-pack'
      ? `multi_ack_detailed side-band-64k ofs-delta shallow agent=${SERVER_AGENT} symref=HEAD:${headTarget(repo)} object-format=sha1`
      : `report-status side-band-64k delete-refs ofs-delta agent=${SERVER_AGENT} object-format=sha1`;
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    const headOid = repo.refs.get(headTarget(repo)) ?? refs[0][1];
    parts.push(pktLine(`${headOid} HEAD\0${caps}\n`));
    for (const [ref, oid] of refs) {
      parts.push(pktLine(`${oid} ${ref}\n`));
      const obj = getObject(repo, oid);
      if (obj && obj.type === 'tag') {
        const peeled = peelToCommit(repo, oid);
        if (peeled) parts.push(pktLine(`${peeled} ${ref}^{}\n`));
      }
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

// The v2 advertisement never changes, so frame it once at startup
// instead of on every info/refs request.
const ADVERTISEMENT_V2 = Buffer.concat([
  pktLine('version 2\n'),
  pktLine(`agent=${SERVER_AGENT}\n`),
  pktLine('ls-refs\n'),
  pktLine('fetch=shallow\n'),
  pktLine('object-format=sha1\n'),
  PKT_FLUSH,
]);

function handleInfoRefs(
  req: IncomingMessage,
  res: ServerResponse,
  repo: Repo,
  url: RequestUrl,
): void {
  const service = url.searchParams.get('service');
  if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
    sendJson(res, 400, { message: 'Unknown service' });
    return;
  }
  const protocol = req.headers['git-protocol'];
  const wantsV2 =
    service === 'git-upload-pack' &&
    typeof protocol === 'string' &&
    protocol.includes('version=2');
  const body = wantsV2 ? ADVERTISEMENT_V2 : advertisementV0(repo, service);
  res.writeHead(200, {
    'content-type': `application/x-${service}-advertisement`,
    'content-length': String(body.length),
    'x-github-request-id': requestId(),
    'cache-control': 'no-cache',
  });
  res.end(body);
}

function lsRefsResponse(repo: Repo, args: string[]): Buffer {
  const peel = args.includes('peel');
  const symrefs = args.includes('symrefs');
  const prefixes = args
    .filter((a) => a.startsWith('ref-prefix '))
    .map((a) => a.slice('ref-prefix '.length));
  const matches = (name: string): boolean =>
    prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const parts: Buffer[] = [];
  const target = headTarget(repo);
  const headOid = repo.refs.get(target);
  if (matches('HEAD')) {
    if (headOid) {
      parts.push(
        pktLine(`${headOid} HEAD${symrefs ? ` symref-target:${target}` : ''}\n`),
      );
    } else {
      parts.push(
        pktLine(`${ZERO_OID} HEAD${symrefs ? ` symref-target:${target}` : ''}\n`),
      );
    }
  }
  for (const [ref, oid] of sortedRefs(repo)) {
    if (!matches(ref)) continue;
    let line = `${oid} ${ref}`;
    if (peel) {
      const obj = getObject(repo, oid);
      if (obj && obj.type === 'tag') {
        const peeled = peelToCommit(repo, oid);
        if (peeled) line += ` peeled:${peeled}`;
      }
    }
    parts.push(pktLine(`${line}\n`));
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

interface FetchArgs {
  wants: string[];
  haves: string[];
  shallow: string[];
  depth: number | null;
  done: boolean;
}

function parseFetchArgs(lines: string[]): FetchArgs {
  const out: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, done: false };
  for (const line of lines) {
    if (line.startsWith('want ')) out.wants.push(line.slice(5).trim());
    else if (line.startsWith('have ')) out.haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) out.shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) {
      const n = Number(line.slice(7).trim());
      if (Number.isFinite(n) && n > 0) out.depth = n;
    } else if (line === 'done') out.done = true;
  }
  return out;
}

function shallowSection(plan: FetchPlan): Buffer[] {
  const parts: Buffer[] = [pktLine('shallow-info\n')];
  for (const oid of plan.boundary) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  parts.push(PKT_FLUSH);
  return parts;
}

function handleUploadPackV2(res: ServerResponse, repo: Repo, body: Buffer): void {
  // A v2 command is: capability pkt-lines, a delim, argument pkt-lines, a
  // flush. Scan the whole body and split the line groups on the delim.
  const groups: string[][] = [[]];
  let pos = 0;
  while (pos + 4 <= body.length) {
    const header = body.toString('ascii', pos, pos + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = parseInt(header, 16);
    if (length === 0) break;
    if (length === 1) {
      groups.push([]);
      pos += 4;
      continue;
    }
    if (length === 2) {
      pos += 4;
      continue;
    }
    if (length < 4 || pos + length > body.length) break;
    groups[groups.length - 1].push(
      body.toString('utf8', pos + 4, pos + length).replace(/\n$/, ''),
    );
    pos += length;
  }
  const capLines = groups[0];
  const argLines = groups.length > 1 ? groups[1] : [];
  const commandLine = capLines.find((l) => l.startsWith('command='));
  const command = commandLine ? commandLine.slice('command='.length) : '';
  if (command === 'ls-refs') {
    const payload = lsRefsResponse(repo, argLines);
    res.writeHead(200, {
      'content-type': 'application/x-git-upload-pack-result',
      'content-length': String(payload.length),
      'x-github-request-id': requestId(),
    });
    res.end(payload);
    return;
  }
  if (command === 'fetch') {
    const args = parseFetchArgs(argLines);
    const { pack, plan } = packForFetch(repo, args.wants, args.haves, args.depth, args.shallow);
    const parts: Buffer[] = [];
    if (args.haves.length > 0) {
      parts.push(pktLine('acknowledgments\n'), pktLine('NAK\n'), PKT_FLUSH);
    }
    if (args.depth !== null || args.shallow.length > 0) {
      parts.push(...shallowSection(plan));
    }
    parts.push(pktLine('packfile\n'), ...sidebandPackets(pack, 1), PKT_FLUSH);
    const payload = Buffer.concat(parts);
    res.writeHead(200, {
      'content-type': 'application/x-git-upload-pack-result',
      'content-length': String(payload.length),
      'x-github-request-id': requestId(),
    });
    res.end(payload);
    return;
  }
  sendJson(res, 400, { message: 'Unknown or malformed git command' });
}

function handleUploadPackV0(res: ServerResponse, repo: Repo, body: Buffer): void {
  const first = decodePkts(body, 0);
  const wantLines: string[] = [];
  for (const token of first.tokens) {
    if (Buffer.isBuffer(token)) wantLines.push(token.toString('utf8').replace(/\n$/, ''));
  }
  const wants = wantLines
    .filter((l) => l.startsWith('want '))
    .map((l) => l.slice(5).split(' ')[0].trim());
  if (wants.length === 0) {
    sendJson(res, 400, { message: 'Malformed upload-pack request' });
    return;
  }
  const second = decodePkts(body, first.end);
  const haveLines: string[] = [];
  for (const token of second.tokens) {
    if (Buffer.isBuffer(token)) haveLines.push(token.toString('utf8').replace(/\n$/, ''));
  }
  const args = parseFetchArgs(haveLines);
  const { pack, plan } = packForFetch(repo, wants, args.haves, args.depth, args.shallow);
  const parts: Buffer[] = [];
  for (const oid of plan.boundary) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  parts.push(pktLine('NAK\n'), ...sidebandPackets(pack, 1), PKT_FLUSH);
  const payload = Buffer.concat(parts);
  res.writeHead(200, {
    'content-type': 'application/x-git-upload-pack-result',
    'content-length': String(payload.length),
    'x-github-request-id': requestId(),
  });
  res.end(payload);
}

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

function handleReceivePack(res: ServerResponse, repo: Repo, body: Buffer): void {
  const decoded = decodePkts(body, 0);
  const commands: PushCommand[] = [];
  for (const token of decoded.tokens) {
    if (!Buffer.isBuffer(token)) continue;
    let line = token.toString('utf8').replace(/\n$/, '');
    const nul = line.indexOf('\0');
    if (nul !== -1) line = line.slice(0, nul);
    const parts = line.split(' ');
    if (parts.length < 3 || !isOid(parts[0]) || !isOid(parts[1])) continue;
    commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts.slice(2).join(' ') });
  }
  const packBytes = body.subarray(decoded.end);
  let unpackError: string | null = null;
  const needsPack = commands.some((c) => c.newOid !== ZERO_OID);
  if (needsPack && packBytes.length > 0) {
    try {
      readPack(repo, packBytes);
    } catch (err) {
      unpackError = err instanceof Error ? err.message : 'error';
    }
  } else if (needsPack && packBytes.length === 0) {
    unpackError = 'no packfile was sent';
  }

  const report: Buffer[] = [
    pktLine(unpackError ? `unpack ${unpackError}\n` : 'unpack ok\n'),
  ];
  for (const command of commands) {
    const fail = (reason: string): void => {
      report.push(pktLine(`ng ${command.ref} ${reason}\n`));
    };
    const succeed = (): void => {
      report.push(pktLine(`ok ${command.ref}\n`));
    };
    if (unpackError) {
      fail('unpack failed');
      continue;
    }
    const current = repo.refs.get(command.ref);
    if (command.newOid === ZERO_OID) {
      // Delete.
      if (current === undefined) {
        fail('reference not found');
      } else {
        repo.refs.delete(command.ref);
        succeed();
      }
      continue;
    }
    if (!getObject(repo, command.newOid)) {
      fail('new object is missing');
      continue;
    }
    if (command.oldOid === ZERO_OID) {
      // Create.
      if (current !== undefined && current !== command.newOid) {
        fail('reference already exists');
        continue;
      }
      repo.refs.set(command.ref, command.newOid);
      succeed();
      continue;
    }
    // Update: must name the current value and move it forward only.
    if (current !== command.oldOid) {
      fail('stale info');
      continue;
    }
    if (command.newOid !== command.oldOid) {
      const newCommit = peelToCommit(repo, command.newOid);
      const oldCommit = peelToCommit(repo, command.oldOid);
      if (newCommit && oldCommit && !isAncestor(repo, oldCommit, newCommit)) {
        fail('non-fast-forward');
        continue;
      }
    }
    repo.refs.set(command.ref, command.newOid);
    succeed();
  }
  report.push(PKT_FLUSH);
  touchRepo(repo);
  const payload = Buffer.concat([
    ...sidebandPackets(Buffer.concat(report), 1),
    PKT_FLUSH,
  ]);
  res.writeHead(200, {
    'content-type': 'application/x-git-receive-pack-result',
    'content-length': String(payload.length),
    'x-github-request-id': requestId(),
  });
  res.end(payload);
}

// The info/refs exchange is answered without reading a request body,
// so it runs synchronously; the dispatcher calls this directly instead
// of going through the async handleGit below.
function handleGitInfoRefs(
  req: IncomingMessage,
  res: ServerResponse,
  owner: string,
  repoName: string,
  url: RequestUrl,
): void {
  if (!authorized(req)) {
    badCredentials(res);
    return;
  }
  const repo = findRepo(owner, repoName);
  if (!repo) {
    notFound(res);
    return;
  }
  handleInfoRefs(req, res, repo, url);
}

async function handleGit(
  req: IncomingMessage,
  res: ServerResponse,
  owner: string,
  repoName: string,
  action: string,
  url: RequestUrl,
): Promise<void> {
  if (!authorized(req)) {
    badCredentials(res);
    return;
  }
  const repo = findRepo(owner, repoName);
  if (!repo) {
    notFound(res);
    return;
  }
  if (action === 'info/refs') {
    handleInfoRefs(req, res, repo, url);
    return;
  }
  const body = await readBody(req);
  if (action === 'git-upload-pack') {
    const protocol = req.headers['git-protocol'];
    if (typeof protocol === 'string' && protocol.includes('version=2')) {
      handleUploadPackV2(res, repo, body);
    } else {
      handleUploadPackV0(res, repo, body);
    }
    return;
  }
  if (action === 'git-receive-pack') {
    handleReceivePack(res, repo, body);
    return;
  }
  notFound(res);
}

// ---------------------------------------------------------------------------
// GraphQL: a small parser for the documents the suite sends
// ---------------------------------------------------------------------------

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'number'; value: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Map<string, GqlValue> };

interface GqlFieldNode {
  kind: 'field';
  alias: string | null;
  name: string;
  args: Map<string, GqlValue>;
  selections: GqlSelection[];
}
type GqlSelection =
  | GqlFieldNode
  | { kind: 'inline'; typeCondition: string | null; selections: GqlSelection[] }
  | { kind: 'spread'; name: string };

interface GqlOperation {
  type: 'query' | 'mutation';
  selections: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperation[];
  fragments: Map<string, { typeCondition: string | null; selections: GqlSelection[] }>;
}

function gqlTokenize(src: string): { kind: string; value: string }[] {
  const tokens: { kind: string; value: string }[] = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') {
      i += 1;
      continue;
    }
    if (ch === '#') {
      while (i < src.length && src[i] !== '\n') i += 1;
      continue;
    }
    if (src.startsWith('...', i)) {
      tokens.push({ kind: 'spread', value: '...' });
      i += 3;
      continue;
    }
    if ('{}():=[]@$!|&'.includes(ch)) {
      tokens.push({ kind: 'punct', value: ch });
      i += 1;
      continue;
    }
    if (ch === '"') {
      if (src.startsWith('"""', i)) {
        const end = src.indexOf('"""', i + 3);
        tokens.push({ kind: 'string', value: src.slice(i + 3, end === -1 ? src.length : end) });
        i = end === -1 ? src.length : end + 3;
        continue;
      }
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) {
          const esc = src[j + 1];
          if (esc === 'n') out += '\n';
          else if (esc === 't') out += '\t';
          else if (esc === 'r') out += '\r';
          else if (esc === 'u') {
            out += String.fromCharCode(parseInt(src.slice(j + 2, j + 6), 16));
            j += 4;
          } else out += esc;
          j += 2;
        } else {
          out += src[j];
          j += 1;
        }
      }
      tokens.push({ kind: 'string', value: out });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      const m = /^-?\d+(\.\d+)?([eE][+-]?\d+)?/.exec(src.slice(i));
      tokens.push({ kind: 'number', value: m ? m[0] : '0' });
      i += m ? m[0].length : 1;
      continue;
    }
    if (/[_A-Za-z]/.test(ch)) {
      const m = /^[_A-Za-z][_0-9A-Za-z]*/.exec(src.slice(i));
      tokens.push({ kind: 'name', value: m ? m[0] : '' });
      i += m ? m[0].length : 1;
      continue;
    }
    i += 1;
  }
  tokens.push({ kind: 'eof', value: '' });
  return tokens;
}

class GqlParser {
  private tokens: { kind: string; value: string }[];
  private pos = 0;

  constructor(src: string) {
    this.tokens = gqlTokenize(src);
  }

  private peek(): { kind: string; value: string } {
    return this.tokens[Math.min(this.pos, this.tokens.length - 1)];
  }
  private next(): { kind: string; value: string } {
    const token = this.peek();
    this.pos += 1;
    return token;
  }
  private expectPunct(value: string): void {
    const token = this.next();
    if (token.kind !== 'punct' || token.value !== value) {
      throw new Error(`expected '${value}' in GraphQL document`);
    }
  }
  private atPunct(value: string): boolean {
    const token = this.peek();
    return token.kind === 'punct' && token.value === value;
  }

  // Skip a balanced (...) group (variable definitions, directive args).
  private skipParens(): void {
    if (!this.atPunct('(')) return;
    let depth = 0;
    do {
      const token = this.next();
      if (token.kind === 'punct' && token.value === '(') depth += 1;
      else if (token.kind === 'punct' && token.value === ')') depth -= 1;
    } while (depth > 0 && this.peek().kind !== 'eof');
  }

  private skipDirectives(): void {
    while (this.atPunct('@')) {
      this.next();
      this.next(); // directive name
      this.skipParens();
    }
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token.kind === 'punct' && token.value === '$') {
      const name = this.next();
      return { kind: 'var', name: name.value };
    }
    if (token.kind === 'string') return { kind: 'string', value: token.value };
    if (token.kind === 'number') return { kind: 'number', value: Number(token.value) };
    if (token.kind === 'name') {
      if (token.value === 'true') return { kind: 'bool', value: true };
      if (token.value === 'false') return { kind: 'bool', value: false };
      if (token.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: token.value };
    }
    if (token.kind === 'punct' && token.value === '[') {
      const items: GqlValue[] = [];
      while (!this.atPunct(']')) items.push(this.parseValue());
      this.expectPunct(']');
      return { kind: 'list', items };
    }
    if (token.kind === 'punct' && token.value === '{') {
      const fields = new Map<string, GqlValue>();
      while (!this.atPunct('}')) {
        const name = this.next();
        this.expectPunct(':');
        fields.set(name.value, this.parseValue());
      }
      this.expectPunct('}');
      return { kind: 'object', fields };
    }
    throw new Error('unexpected token in GraphQL value');
  }

  private parseArguments(): Map<string, GqlValue> {
    const args = new Map<string, GqlValue>();
    if (!this.atPunct('(')) return args;
    this.next();
    while (!this.atPunct(')')) {
      const name = this.next();
      this.expectPunct(':');
      args.set(name.value, this.parseValue());
    }
    this.expectPunct(')');
    return args;
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expectPunct('{');
    const selections: GqlSelection[] = [];
    while (!this.atPunct('}')) {
      if (this.peek().kind === 'eof') throw new Error('unterminated selection set');
      if (this.peek().kind === 'spread') {
        this.next();
        const head = this.peek();
        if (head.kind === 'name' && head.value === 'on') {
          this.next();
          const typeName = this.next().value;
          this.skipDirectives();
          selections.push({
            kind: 'inline',
            typeCondition: typeName,
            selections: this.parseSelectionSet(),
          });
        } else {
          const name = this.next().value;
          this.skipDirectives();
          selections.push({ kind: 'spread', name });
        }
        continue;
      }
      const first = this.next();
      let alias: string | null = null;
      let name = first.value;
      if (this.atPunct(':')) {
        this.next();
        alias = name;
        name = this.next().value;
      }
      const args = this.parseArguments();
      this.skipDirectives();
      let sub: GqlSelection[] = [];
      if (this.atPunct('{')) sub = this.parseSelectionSet();
      selections.push({ kind: 'field', alias, name, args, selections: sub });
    }
    this.expectPunct('}');
    return selections;
  }

  parseDocument(): GqlDocument {
    const operations: GqlOperation[] = [];
    const fragments = new Map<string, { typeCondition: string | null; selections: GqlSelection[] }>();
    while (this.peek().kind !== 'eof') {
      const token = this.peek();
      if (token.kind === 'punct' && token.value === '{') {
        operations.push({ type: 'query', selections: this.parseSelectionSet() });
        continue;
      }
      if (token.kind === 'name' && (token.value === 'query' || token.value === 'mutation')) {
        const type = token.value as 'query' | 'mutation';
        this.next();
        if (this.peek().kind === 'name') this.next(); // operation name
        this.skipParens(); // variable definitions
        this.skipDirectives();
        operations.push({ type, selections: this.parseSelectionSet() });
        continue;
      }
      if (token.kind === 'name' && token.value === 'fragment') {
        this.next();
        const name = this.next().value;
        const on = this.next();
        void on;
        const typeName = this.next().value;
        this.skipDirectives();
        fragments.set(name, {
          typeCondition: typeName,
          selections: this.parseSelectionSet(),
        });
        continue;
      }
      this.next(); // skip anything unexpected rather than failing the request
    }
    return { operations, fragments };
  }
}

function resolveGqlValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'var':
      return variables[value.name];
    case 'string':
    case 'number':
    case 'bool':
    case 'enum':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.items.map((item) => resolveGqlValue(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [key, item] of value.fields) out[key] = resolveGqlValue(item, variables);
      return out;
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL: schema surface and executor
// ---------------------------------------------------------------------------

type GqlSource = Record<string, unknown> & { __typename: string };

interface GqlCtx {
  errors: { message: string }[];
  variables: Record<string, unknown>;
  doc: GqlDocument;
}

function globalId(kind: string, a: number | string, b: number | string = ''): string {
  return b64Encode(`ghclone:${kind}:${a}:${b}`);
}

function decodeGlobalId(id: string): { kind: string; a: string; b: string } | null {
  try {
    const text = b64Decode(id);
    const parts = text.split(':');
    if (parts.length !== 4 || parts[0] !== 'ghclone') return null;
    return { kind: parts[1], a: parts[2], b: parts[3] };
  } catch {
    return null;
  }
}

function repoByDbId(dbId: number): Repo | null {
  for (const repo of reposByName.values()) {
    if (repo.dbId === dbId) return repo;
  }
  return null;
}

const userSource = (): GqlSource => ({ __typename: 'User' });
const repoSource = (repo: Repo): GqlSource => ({ __typename: 'Repository', repo });
const issueSource = (repo: Repo, issue: IssueRec): GqlSource => ({
  __typename: 'Issue',
  repo,
  issue,
});
const pullSource = (repo: Repo, pull: PullRec): GqlSource => ({
  __typename: 'PullRequest',
  repo,
  pull,
});
const commentSource = (repo: Repo, number: number, comment: CommentRec): GqlSource => ({
  __typename: 'IssueComment',
  repo,
  number,
  comment,
});

function cursorFor(number: number): string {
  return b64Encode(`cursor:${number}`);
}
function numberFromCursor(cursor: unknown): number | null {
  if (typeof cursor !== 'string') return null;
  try {
    const text = b64Decode(cursor);
    const m = /^cursor:(\d+)$/.exec(text);
    return m ? Number(m[1]) : null;
  } catch {
    return null;
  }
}

interface ConnectionMade {
  nodes: GqlSource[];
  pageInfo: Record<string, unknown>;
  totalCount: number;
}

function makeConnection<T>(
  items: T[],
  args: Record<string, unknown>,
  keyOf: (item: T) => number,
  wrap: (item: T) => GqlSource,
): ConnectionMade {
  const after = numberFromCursor(args.after);
  let start = 0;
  if (after !== null) {
    const idx = items.findIndex((item) => keyOf(item) === after);
    start = idx === -1 ? 0 : idx + 1;
  }
  const first =
    typeof args.first === 'number' && Number.isFinite(args.first)
      ? Math.max(0, Math.floor(args.first))
      : items.length;
  const slice = items.slice(start, start + first);
  const hasNext = start + slice.length < items.length;
  return {
    nodes: slice.map(wrap),
    pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: hasNext,
      hasPreviousPage: start > 0,
      startCursor: slice.length ? cursorFor(keyOf(slice[0])) : null,
      endCursor: slice.length ? cursorFor(keyOf(slice[slice.length - 1])) : null,
    },
    totalCount: items.length,
  };
}

function repoFilesChanges(repo: Repo, pull: PullRec): FileChange[] {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`);
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  if (!headTip || !baseTip) return [];
  const base = mergeBase(repo, headTip, baseTip) ?? peelToCommit(repo, baseTip);
  const headCommit = peelToCommit(repo, headTip);
  if (!base || !headCommit) return [];
  const baseObj = getObject(repo, base);
  const headObj = getObject(repo, headCommit);
  if (!baseObj || !headObj) return [];
  return diffTrees(repo, parseCommit(baseObj.data).tree, parseCommit(headObj.data).tree);
}

function createIssueRecord(repo: Repo, title: string, body: string, labels: string[]): IssueRec {
  repo.numberSeq += 1;
  gidSeq += 1;
  const now = tick();
  const issue: IssueRec = {
    number: repo.numberSeq,
    gid: gidSeq,
    title,
    body,
    state: 'open',
    labels,
    comments: [],
    createdSec: now,
    updatedSec: now,
    closedSec: null,
  };
  repo.issues.set(issue.number, issue);
  touchRepo(repo);
  return issue;
}

function createPullRecord(
  repo: Repo,
  title: string,
  body: string,
  headRef: string,
  baseRef: string,
): PullRec {
  repo.numberSeq += 1;
  gidSeq += 1;
  const now = tick();
  const pull: PullRec = {
    number: repo.numberSeq,
    gid: gidSeq,
    title,
    body,
    state: 'open',
    merged: false,
    headRef,
    baseRef,
    comments: [],
    createdSec: now,
    updatedSec: now,
    mergedSec: null,
    mergeSha: null,
  };
  repo.pulls.set(pull.number, pull);
  touchRepo(repo);
  return pull;
}

type Resolver = (
  source: GqlSource,
  args: Record<string, unknown>,
  ctx: GqlCtx,
) => unknown;

const gqlResolvers: Record<string, Record<string, Resolver>> = {
  Query: {
    viewer: () => userSource(),
    repository: (_s, args) => {
      const repo = findRepo(String(args.owner ?? ''), String(args.name ?? ''));
      return repo ? repoSource(repo) : null;
    },
    node: (_s, args) => {
      const decoded = decodeGlobalId(String(args.id ?? ''));
      if (!decoded) return null;
      if (decoded.kind === 'Repository') {
        const repo = repoByDbId(Number(decoded.a));
        return repo ? repoSource(repo) : null;
      }
      if (decoded.kind === 'Issue') {
        const repo = repoByDbId(Number(decoded.a));
        const issue = repo?.issues.get(Number(decoded.b));
        return repo && issue ? issueSource(repo, issue) : null;
      }
      if (decoded.kind === 'PullRequest') {
        const repo = repoByDbId(Number(decoded.a));
        const pull = repo?.pulls.get(Number(decoded.b));
        return repo && pull ? pullSource(repo, pull) : null;
      }
      if (decoded.kind === 'IssueComment') {
        const repo = repoByDbId(Number(decoded.a));
        if (!repo) return null;
        for (const target of [...repo.issues.values(), ...repo.pulls.values()]) {
          const comment = target.comments.find((c) => c.id === Number(decoded.b));
          if (comment) return commentSource(repo, target.number, comment);
        }
        return null;
      }
      return null;
    },
    __type: (_s, args) => {
      const name = String(args.name ?? '');
      if (!GQL_TYPE_FIELDS[name] && !GQL_ENUM_VALUES[name]) return null;
      return { __typename: '__Type', typeName: name };
    },
    __schema: () => ({ __typename: '__Schema' }),
  },
  Mutation: {
    createIssue: (_s, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const decoded = decodeGlobalId(String(input.repositoryId ?? ''));
      const repo = decoded ? repoByDbId(Number(decoded.a)) : null;
      if (!repo) {
        ctx.errors.push({ message: 'repository not found for createIssue' });
        return { __typename: 'CreateIssuePayload', issue: null, clientMutationId: null };
      }
      const issue = createIssueRecord(
        repo,
        typeof input.title === 'string' ? input.title : '',
        typeof input.body === 'string' ? input.body : '',
        [],
      );
      return {
        __typename: 'CreateIssuePayload',
        issue: issueSource(repo, issue),
        clientMutationId: null,
      };
    },
    closeIssue: (_s, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const decoded = decodeGlobalId(String(input.issueId ?? ''));
      const repo = decoded ? repoByDbId(Number(decoded.a)) : null;
      const issue = repo?.issues.get(Number(decoded?.b));
      if (!repo || !issue) {
        ctx.errors.push({ message: 'issue not found for closeIssue' });
        return { __typename: 'CloseIssuePayload', issue: null, clientMutationId: null };
      }
      issue.state = 'closed';
      issue.closedSec = tick();
      issue.updatedSec = issue.closedSec;
      return {
        __typename: 'CloseIssuePayload',
        issue: issueSource(repo, issue),
        clientMutationId: null,
      };
    },
    createPullRequest: (_s, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const decoded = decodeGlobalId(String(input.repositoryId ?? ''));
      const repo = decoded ? repoByDbId(Number(decoded.a)) : null;
      const head = String(input.headRefName ?? '');
      const base = String(input.baseRefName ?? '');
      if (
        !repo ||
        !repo.refs.has(`refs/heads/${head}`) ||
        !repo.refs.has(`refs/heads/${base}`)
      ) {
        ctx.errors.push({ message: 'head or base branch not found for createPullRequest' });
        return {
          __typename: 'CreatePullRequestPayload',
          pullRequest: null,
          clientMutationId: null,
        };
      }
      for (const pull of repo.pulls.values()) {
        if (pull.state === 'open' && pull.headRef === head && pull.baseRef === base) {
          return {
            __typename: 'CreatePullRequestPayload',
            pullRequest: pullSource(repo, pull),
            clientMutationId: null,
          };
        }
      }
      const pull = createPullRecord(
        repo,
        typeof input.title === 'string' ? input.title : '',
        typeof input.body === 'string' ? input.body : '',
        head,
        base,
      );
      return {
        __typename: 'CreatePullRequestPayload',
        pullRequest: pullSource(repo, pull),
        clientMutationId: null,
      };
    },
    mergePullRequest: (_s, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const decoded = decodeGlobalId(String(input.pullRequestId ?? ''));
      const repo = decoded ? repoByDbId(Number(decoded.a)) : null;
      const pull = repo?.pulls.get(Number(decoded?.b));
      if (!repo || !pull) {
        ctx.errors.push({ message: 'pull request not found for mergePullRequest' });
        return {
          __typename: 'MergePullRequestPayload',
          pullRequest: null,
          clientMutationId: null,
        };
      }
      if (!pull.merged) {
        const result = performMerge(repo, pull);
        if (!result.ok) {
          ctx.errors.push({ message: `pull request is not mergeable: ${result.reason}` });
        }
      }
      return {
        __typename: 'MergePullRequestPayload',
        pullRequest: pullSource(repo, pull),
        clientMutationId: null,
      };
    },
    addComment: (_s, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const decoded = decodeGlobalId(String(input.subjectId ?? ''));
      const repo = decoded ? repoByDbId(Number(decoded.a)) : null;
      const target = repo
        ? (repo.issues.get(Number(decoded?.b)) ?? repo.pulls.get(Number(decoded?.b)))
        : undefined;
      if (!repo || !target) {
        ctx.errors.push({ message: 'subject not found for addComment' });
        return { __typename: 'AddCommentPayload', commentEdge: null, clientMutationId: null };
      }
      repo.commentSeq += 1;
      const now = tick();
      const comment: CommentRec = {
        id: repo.commentSeq,
        body: typeof input.body === 'string' ? input.body : '',
        createdSec: now,
        updatedSec: now,
      };
      target.comments.push(comment);
      return {
        __typename: 'AddCommentPayload',
        commentEdge: {
          __typename: 'IssueCommentEdge',
          node: commentSource(repo, target.number, comment),
          cursor: cursorFor(comment.id),
        },
        clientMutationId: null,
      };
    },
  },
  User: {
    login: () => VIEWER.login,
    id: () => globalId('User', VIEWER.id),
    name: () => VIEWER.name,
    email: () => VIEWER.email,
  },
  Repository: {
    id: (s) => globalId('Repository', (s.repo as Repo).dbId),
    databaseId: (s) => (s.repo as Repo).dbId,
    name: (s) => (s.repo as Repo).name,
    nameWithOwner: (s) => `${VIEWER.login}/${(s.repo as Repo).name}`,
    description: (s) => (s.repo as Repo).description,
    isPrivate: (s) => (s.repo as Repo).priv,
    owner: () => userSource(),
    defaultBranchRef: (s) => {
      const repo = s.repo as Repo;
      if (repo.refs.size === 0) return null;
      return { __typename: 'Ref', repo, name: repo.defaultBranch };
    },
    viewerPermission: () => 'ADMIN',
    hasIssuesEnabled: () => true,
    createdAt: (s) => isoOf((s.repo as Repo).createdSec),
    updatedAt: (s) => isoOf((s.repo as Repo).updatedSec),
    url: (s) => `https://forge.invalid/${VIEWER.login}/${(s.repo as Repo).name}`,
    issue: (s, args) => {
      const repo = s.repo as Repo;
      const issue = repo.issues.get(Number(args.number));
      return issue ? issueSource(repo, issue) : null;
    },
    issues: (s, args) => {
      const repo = s.repo as Repo;
      let issues = [...repo.issues.values()];
      const states = Array.isArray(args.states) ? (args.states as string[]) : null;
      if (states && states.length > 0) {
        issues = issues.filter((i) =>
          states.includes(i.state === 'open' ? 'OPEN' : 'CLOSED'),
        );
      }
      const orderBy = (args.orderBy ?? null) as
        | { field?: string; direction?: string }
        | null;
      const descending = orderBy ? orderBy.direction !== 'ASC' : false;
      issues.sort((a, b) =>
        descending ? b.number - a.number : a.number - b.number,
      );
      const made = makeConnection(issues, args, (i) => i.number, (i) => issueSource(repo, i));
      return {
        __typename: 'IssueConnection',
        nodes: made.nodes,
        pageInfo: made.pageInfo,
        totalCount: made.totalCount,
      };
    },
    pullRequest: (s, args) => {
      const repo = s.repo as Repo;
      const pull = repo.pulls.get(Number(args.number));
      return pull ? pullSource(repo, pull) : null;
    },
    pullRequests: (s, args) => {
      const repo = s.repo as Repo;
      let pulls = [...repo.pulls.values()];
      const states = Array.isArray(args.states) ? (args.states as string[]) : null;
      if (states && states.length > 0) {
        pulls = pulls.filter((p) =>
          states.includes(p.merged ? 'MERGED' : p.state === 'open' ? 'OPEN' : 'CLOSED'),
        );
      }
      pulls.sort((a, b) => b.number - a.number);
      const made = makeConnection(pulls, args, (p) => p.number, (p) => pullSource(repo, p));
      return {
        __typename: 'PullRequestConnection',
        nodes: made.nodes,
        pageInfo: made.pageInfo,
        totalCount: made.totalCount,
      };
    },
  },
  Issue: {
    id: (s) => globalId('Issue', (s.repo as Repo).dbId, (s.issue as IssueRec).number),
    number: (s) => (s.issue as IssueRec).number,
    title: (s) => (s.issue as IssueRec).title,
    body: (s) => (s.issue as IssueRec).body,
    state: (s) => ((s.issue as IssueRec).state === 'open' ? 'OPEN' : 'CLOSED'),
    createdAt: (s) => isoOf((s.issue as IssueRec).createdSec),
    updatedAt: (s) => isoOf((s.issue as IssueRec).updatedSec),
    closedAt: (s) => {
      const issue = s.issue as IssueRec;
      return issue.closedSec === null ? null : isoOf(issue.closedSec);
    },
    author: () => userSource(),
    repository: (s) => repoSource(s.repo as Repo),
    url: (s) =>
      `https://forge.invalid/${VIEWER.login}/${(s.repo as Repo).name}/issues/${(s.issue as IssueRec).number}`,
  },
  PullRequest: {
    id: (s) => globalId('PullRequest', (s.repo as Repo).dbId, (s.pull as PullRec).number),
    number: (s) => (s.pull as PullRec).number,
    title: (s) => (s.pull as PullRec).title,
    body: (s) => (s.pull as PullRec).body,
    state: (s) => {
      const pull = s.pull as PullRec;
      return pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED';
    },
    merged: (s) => (s.pull as PullRec).merged,
    mergedAt: (s) => {
      const pull = s.pull as PullRec;
      return pull.mergedSec === null ? null : isoOf(pull.mergedSec);
    },
    headRefName: (s) => (s.pull as PullRec).headRef,
    baseRefName: (s) => (s.pull as PullRec).baseRef,
    mergeable: (s) => {
      const repo = s.repo as Repo;
      const pull = s.pull as PullRec;
      if (pull.merged) return 'MERGEABLE';
      if (pull.state !== 'open') return 'UNKNOWN';
      return attemptMerge(repo, pull).ok ? 'MERGEABLE' : 'CONFLICTING';
    },
    createdAt: (s) => isoOf((s.pull as PullRec).createdSec),
    updatedAt: (s) => isoOf((s.pull as PullRec).updatedSec),
    author: () => userSource(),
    repository: (s) => repoSource(s.repo as Repo),
    files: (s, args) => {
      const repo = s.repo as Repo;
      const pull = s.pull as PullRec;
      const changes = repoFilesChanges(repo, pull);
      const first =
        typeof args.first === 'number' ? Math.max(0, Math.floor(args.first)) : changes.length;
      return {
        __typename: 'PullRequestChangedFileConnection',
        nodes: changes.slice(0, first).map((change) => ({
          __typename: 'PullRequestChangedFile',
          path: change.filename,
          additions: change.additions,
          deletions: change.deletions,
          changeType:
            change.status === 'added'
              ? 'ADDED'
              : change.status === 'removed'
                ? 'DELETED'
                : 'MODIFIED',
        })),
        totalCount: changes.length,
      };
    },
  },
  Ref: {
    name: (s) => s.name as string,
    prefix: () => 'refs/heads/',
    target: (s) => {
      const repo = s.repo as Repo;
      const oid = repo.refs.get(`refs/heads/${s.name as string}`);
      if (!oid) return null;
      const commit = peelToCommit(repo, oid);
      return commit ? { __typename: 'Commit', repo, oid: commit } : null;
    },
  },
  Commit: {
    oid: (s) => s.oid as string,
    message: (s) => {
      const obj = getObject(s.repo as Repo, s.oid as string);
      return obj ? parseCommit(obj.data).message : '';
    },
    committedDate: (s) => {
      const obj = getObject(s.repo as Repo, s.oid as string);
      return obj ? isoOf(parseCommit(obj.data).timeSec) : null;
    },
  },
  IssueComment: {
    id: (s) => globalId('IssueComment', (s.repo as Repo).dbId, (s.comment as CommentRec).id),
    body: (s) => (s.comment as CommentRec).body,
    createdAt: (s) => isoOf((s.comment as CommentRec).createdSec),
    updatedAt: (s) => isoOf((s.comment as CommentRec).updatedSec),
    author: () => userSource(),
  },
  __Type: {
    name: (s) => s.typeName as string,
    kind: (s) => (GQL_ENUM_VALUES[s.typeName as string] ? 'ENUM' : 'OBJECT'),
    fields: (s) =>
      (GQL_TYPE_FIELDS[s.typeName as string] ?? []).map((name) => ({
        __typename: '__Field',
        name,
      })),
    enumValues: (s) =>
      (GQL_ENUM_VALUES[s.typeName as string] ?? []).map((name) => ({
        __typename: '__EnumValue',
        name,
      })),
  },
  __Schema: {
    queryType: () => ({ __typename: '__Type', typeName: 'Query' }),
    mutationType: () => ({ __typename: '__Type', typeName: 'Mutation' }),
    types: () =>
      [...Object.keys(GQL_TYPE_FIELDS), ...Object.keys(GQL_ENUM_VALUES)].map((name) => ({
        __typename: '__Type',
        typeName: name,
      })),
  },
};

const GQL_TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', 'search', 'rateLimit'],
  Mutation: [
    'createIssue',
    'closeIssue',
    'createPullRequest',
    'mergePullRequest',
    'addComment',
    'updateIssue',
  ],
  User: ['login', 'id', 'name', 'email', 'url', 'createdAt'],
  Repository: [
    'id',
    'databaseId',
    'name',
    'nameWithOwner',
    'owner',
    'defaultBranchRef',
    'viewerPermission',
    'hasIssuesEnabled',
    'issue',
    'issues',
    'pullRequests',
    'pullRequest',
    'description',
    'isPrivate',
    'createdAt',
    'updatedAt',
    'url',
    'labels',
    'ref',
    'refs',
  ],
  Issue: [
    'id',
    'number',
    'title',
    'state',
    'body',
    'createdAt',
    'updatedAt',
    'closedAt',
    'author',
    'repository',
    'labels',
    'comments',
    'url',
  ],
  PullRequest: [
    'id',
    'number',
    'headRefName',
    'baseRefName',
    'mergeable',
    'state',
    'merged',
    'files',
    'title',
    'body',
    'createdAt',
    'updatedAt',
    'mergedAt',
    'author',
    'repository',
    'mergeCommit',
    'url',
  ],
  Ref: ['name', 'prefix', 'target'],
  Commit: ['oid', 'message', 'committedDate', 'author', 'tree'],
  IssueConnection: ['nodes', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'pageInfo', 'totalCount'],
  PullRequestChangedFileConnection: ['nodes', 'totalCount'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changeType'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  IssueComment: ['id', 'body', 'createdAt', 'updatedAt', 'author'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'clientMutationId'],
  IssueCommentEdge: ['node', 'cursor'],
  __Type: ['name', 'kind', 'fields', 'enumValues', 'description'],
  __Field: ['name', 'description', 'args', 'type'],
  __EnumValue: ['name', 'description'],
  __Schema: ['types', 'queryType', 'mutationType'],
};

const GQL_ENUM_VALUES: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
};

function isGqlSource(value: unknown): value is GqlSource {
  return (
    typeof value === 'object' &&
    value !== null &&
    typeof (value as { __typename?: unknown }).__typename === 'string'
  );
}

function execSelectionSet(
  typeName: string,
  source: GqlSource,
  selections: GqlSelection[],
  ctx: GqlCtx,
): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const selection of selections) {
    if (selection.kind === 'inline') {
      if (!selection.typeCondition || selection.typeCondition === typeName) {
        Object.assign(out, execSelectionSet(typeName, source, selection.selections, ctx));
      }
      continue;
    }
    if (selection.kind === 'spread') {
      const fragment = ctx.doc.fragments.get(selection.name);
      if (fragment && (!fragment.typeCondition || fragment.typeCondition === typeName)) {
        Object.assign(out, execSelectionSet(typeName, source, fragment.selections, ctx));
      }
      continue;
    }
    const key = selection.alias ?? selection.name;
    if (selection.name === '__typename') {
      out[key] = typeName;
      continue;
    }
    const args: Record<string, unknown> = {};
    for (const [argName, argValue] of selection.args) {
      args[argName] = resolveGqlValue(argValue, ctx.variables);
    }
    const resolver = gqlResolvers[typeName]?.[selection.name];
    let value: unknown;
    if (resolver) {
      value = resolver(source, args, ctx);
    } else if (selection.name in source) {
      value = source[selection.name];
    } else {
      ctx.errors.push({
        message: `Field '${selection.name}' doesn't exist on type '${typeName}'`,
      });
      out[key] = null;
      continue;
    }
    out[key] = completeGqlValue(value, selection.selections, ctx);
  }
  return out;
}

function completeGqlValue(
  value: unknown,
  selections: GqlSelection[],
  ctx: GqlCtx,
): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) {
    return value.map((item) => completeGqlValue(item, selections, ctx));
  }
  if (isGqlSource(value)) {
    if (selections.length === 0) return {};
    return execSelectionSet(value.__typename, value, selections, ctx);
  }
  return value;
}

function runGraphqlOperation(
  operation: GqlOperation,
  variables: Record<string, unknown>,
  doc: GqlDocument,
): Record<string, unknown> {
  const ctx: GqlCtx = { errors: [], variables, doc };
  const rootType = operation.type === 'mutation' ? 'Mutation' : 'Query';
  const root: GqlSource = { __typename: rootType };
  const data = execSelectionSet(rootType, root, operation.selections, ctx);
  const envelope: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) envelope.errors = ctx.errors;
  return envelope;
}

async function handleGraphql(
  req: IncomingMessage,
  res: ServerResponse,
  rawBody: Buffer,
): Promise<void> {
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(rawBody.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return;
  }
  const runOne = (entry: unknown): Record<string, unknown> => {
    const item = (entry ?? {}) as {
      query?: unknown;
      variables?: unknown;
      operationName?: unknown;
    };
    if (typeof item.query !== 'string') {
      return { data: null, errors: [{ message: 'query must be a string' }] };
    }
    const variables =
      item.variables && typeof item.variables === 'object'
        ? (item.variables as Record<string, unknown>)
        : {};
    let doc: GqlDocument;
    try {
      doc = new GqlParser(item.query).parseDocument();
    } catch (err) {
      return {
        data: null,
        errors: [{ message: err instanceof Error ? err.message : 'parse error' }],
      };
    }
    const operation =
      doc.operations.find(
        (op) =>
          typeof item.operationName !== 'string' ||
          op.type === item.operationName ||
          doc.operations.length === 1,
      ) ?? doc.operations[0];
    if (!operation) {
      return { data: null, errors: [{ message: 'no operation in document' }] };
    }
    return runGraphqlOperation(operation, variables, doc);
  };
  if (Array.isArray(parsed)) {
    sendJson(res, 200, parsed.map(runOne));
    return;
  }
  sendJson(res, 200, runOne(parsed));
}

// ---------------------------------------------------------------------------
// MCP (streamable HTTP, JSON-RPC 2.0)
// ---------------------------------------------------------------------------

const MCP_SERVER_INFO = { name: 'makefun-forge', version: FORGE_VERSION };
const MCP_PROTOCOL_VERSIONS = ['2026-07-28', '2025-11-25'];

interface McpTool {
  name: string;
  description: string;
  inputSchema: Record<string, unknown>;
}

const MCP_TOOLS: McpTool[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name.' },
        description: { type: 'string', description: 'Repository description.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Open an issue on a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        title: { type: 'string', description: 'Issue title.' },
        body: { type: 'string', description: 'Issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        title: { type: 'string', description: 'Pull request title.' },
        body: { type: 'string', description: 'Pull request body.' },
        head: { type: 'string', description: 'Head branch name.' },
        base: { type: 'string', description: 'Base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request into its base branch (squash).',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        pull_number: { type: 'number', description: 'Pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpRepoView(repo: Repo): Record<string, unknown> {
  return {
    id: repo.dbId,
    name: repo.name,
    full_name: `${VIEWER.login}/${repo.name}`,
    owner: { login: VIEWER.login, id: VIEWER.id },
    private: repo.priv,
    description: repo.description,
    default_branch: repo.defaultBranch,
    created_at: isoOf(repo.createdSec),
    updated_at: isoOf(repo.updatedSec),
  };
}

function mcpIssueView(repo: Repo, issue: IssueRec): Record<string, unknown> {
  return {
    id: issue.gid,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => ({ name })),
    user: { login: VIEWER.login },
    created_at: isoOf(issue.createdSec),
    updated_at: isoOf(issue.updatedSec),
  };
}

function mcpPullView(repo: Repo, pull: PullRec): Record<string, unknown> {
  return {
    id: pull.gid,
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    head: { ref: pull.headRef, sha: repo.refs.get(`refs/heads/${pull.headRef}`) ?? null },
    base: { ref: pull.baseRef, sha: repo.refs.get(`refs/heads/${pull.baseRef}`) ?? null },
    merged: pull.merged,
    merged_at: pull.mergedSec === null ? null : isoOf(pull.mergedSec),
    merge_commit_sha: pull.mergeSha,
  };
}

class McpCallError extends Error {
  code: number;
  constructor(code: number, message: string) {
    super(message);
    this.code = code;
  }
}

function requireArgs(
  tool: McpTool,
  args: Record<string, unknown>,
): Record<string, unknown> {
  const schema = tool.inputSchema as { required?: string[] };
  for (const name of schema.required ?? []) {
    if (args[name] === undefined || args[name] === null || args[name] === '') {
      throw new McpCallError(-32602, `missing required argument '${name}' for tool '${tool.name}'`);
    }
  }
  return args;
}

function mcpToolResult(value: unknown): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify(value) }],
    structuredContent: value as Record<string, unknown>,
    isError: false,
  };
}

function mcpToolError(message: string): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: message }],
    isError: true,
  };
}

function callMcpTool(name: string, rawArgs: unknown): Record<string, unknown> {
  const tool = MCP_TOOLS.find((t) => t.name === name);
  if (!tool) throw new McpCallError(-32602, `unknown tool '${name}'`);
  const args = requireArgs(
    tool,
    rawArgs && typeof rawArgs === 'object' ? (rawArgs as Record<string, unknown>) : {},
  );
  const repoOf = (): Repo => {
    const repo = findRepo(String(args.owner ?? ''), String(args.repo ?? ''));
    if (!repo) throw new McpCallError(-32602, 'repository not found');
    return repo;
  };
  switch (name) {
    case 'create_repo': {
      const repoName = String(args.name);
      const existing = reposByName.get(repoName);
      if (existing) return mcpToolResult(mcpRepoView(existing));
      const repo = newRepo(
        repoName,
        typeof args.description === 'string' ? args.description : '',
        args.private === true,
      );
      reposByName.set(repoName, repo);
      return mcpToolResult(mcpRepoView(repo));
    }
    case 'get_repo': {
      return mcpToolResult(mcpRepoView(repoOf()));
    }
    case 'create_issue': {
      const repo = repoOf();
      const issue = createIssueRecord(
        repo,
        String(args.title),
        typeof args.body === 'string' ? args.body : '',
        [],
      );
      return mcpToolResult(mcpIssueView(repo, issue));
    }
    case 'list_issues': {
      const repo = repoOf();
      const state = typeof args.state === 'string' ? args.state : 'open';
      let issues = [...repo.issues.values()];
      if (state === 'open') issues = issues.filter((i) => i.state === 'open');
      else if (state === 'closed') issues = issues.filter((i) => i.state === 'closed');
      issues.sort((a, b) => a.number - b.number);
      return mcpToolResult(issues.map((i) => mcpIssueView(repo, i)));
    }
    case 'create_pull_request': {
      const repo = repoOf();
      const head = stripOwnerPrefix(String(args.head));
      const base = stripOwnerPrefix(String(args.base));
      if (!repo.refs.has(`refs/heads/${head}`) || !repo.refs.has(`refs/heads/${base}`)) {
        return mcpToolError('head or base branch does not exist');
      }
      for (const pull of repo.pulls.values()) {
        if (pull.state === 'open' && pull.headRef === head && pull.baseRef === base) {
          return mcpToolResult(mcpPullView(repo, pull));
        }
      }
      const pull = createPullRecord(
        repo,
        String(args.title),
        typeof args.body === 'string' ? args.body : '',
        head,
        base,
      );
      return mcpToolResult(mcpPullView(repo, pull));
    }
    case 'merge_pull_request': {
      const repo = repoOf();
      const pull = repo.pulls.get(Number(args.pull_number));
      if (!pull) return mcpToolError('pull request not found');
      if (!pull.merged) {
        const result = performMerge(repo, pull);
        if (!result.ok) return mcpToolError(`pull request is not mergeable: ${result.reason}`);
      }
      return mcpToolResult({
        ...mcpPullView(repo, pull),
        merged: true,
        message: 'Pull Request successfully merged',
      });
    }
    default:
      throw new McpCallError(-32602, `unknown tool '${name}'`);
  }
}

function mcpDiscoverResult(): Record<string, unknown> {
  return {
    supportedVersions: MCP_PROTOCOL_VERSIONS,
    capabilities: { tools: {} },
    serverInfo: MCP_SERVER_INFO,
    _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
  };
}

async function handleMcp(
  req: IncomingMessage,
  res: ServerResponse,
  rawBody: Buffer,
): Promise<void> {
  if (!authorized(req)) {
    sendJson(res, 401, {
      jsonrpc: '2.0',
      id: null,
      error: { code: -32001, message: 'unauthorized' },
    });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(rawBody.toString('utf8'));
  } catch {
    sendJson(res, 400, {
      jsonrpc: '2.0',
      id: null,
      error: { code: -32700, message: 'Parse error' },
    });
    return;
  }
  const message = (parsed ?? {}) as {
    jsonrpc?: unknown;
    id?: unknown;
    method?: unknown;
    params?: unknown;
  };
  const isNotification = message.id === undefined;
  const reply = (payload: Record<string, unknown>): void => {
    if (isNotification) {
      sendEmpty(res, 202);
      return;
    }
    sendJson(res, 200, { jsonrpc: '2.0', id: message.id ?? null, ...payload });
  };
  const method = typeof message.method === 'string' ? message.method : '';
  const params =
    message.params && typeof message.params === 'object'
      ? (message.params as Record<string, unknown>)
      : {};
  try {
    switch (method) {
      case 'server/discover':
        return reply({ result: mcpDiscoverResult() });
      case 'initialize': {
        const requested = params.protocolVersion;
        return reply({
          result: {
            protocolVersion:
              typeof requested === 'string' && MCP_PROTOCOL_VERSIONS.includes(requested)
                ? requested
                : MCP_PROTOCOL_VERSIONS[1],
            capabilities: { tools: {} },
            serverInfo: MCP_SERVER_INFO,
          },
        });
      }
      case 'ping':
        return reply({ result: {} });
      case 'tools/list':
        return reply({ result: { tools: MCP_TOOLS } });
      case 'tools/call': {
        const toolName = typeof params.name === 'string' ? params.name : '';
        const result = callMcpTool(toolName, params.arguments ?? {});
        return reply({ result });
      }
      default:
        if (isNotification) return sendEmpty(res, 202);
        return reply({
          error: { code: -32601, message: `method not found: ${method}` },
        });
    }
  } catch (err) {
    if (err instanceof McpCallError) {
      return reply({ error: { code: err.code, message: err.message } });
    }
    return reply({
      error: { code: -32603, message: err instanceof Error ? err.message : 'internal error' },
    });
  }
}

// ---------------------------------------------------------------------------
// Top-level routing
// ---------------------------------------------------------------------------

function decodeSegment(segment: string): string {
  // Decoding only does something when a '%' introduces an escape, so the
  // common case skips the call (and its exception handler) entirely.
  if (!segment.includes('%')) return segment;
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

const EMPTY_BODY = Buffer.alloc(0);

// Whether a request can carry a body worth reading: it uses one of the
// methods this API accepts bodies on, or it frames a body explicitly.
// Anything else (a plain GET, a bare DELETE) is answered without waiting
// for a body stream that has nothing in it.
function requestMayHaveBody(req: IncomingMessage): boolean {
  if (req.method === 'POST' || req.method === 'PUT' || req.method === 'PATCH') {
    return true;
  }
  const length = req.headers['content-length'];
  if (length !== undefined && length !== '0') return true;
  return req.headers['transfer-encoding'] !== undefined;
}

// Characters that make the WHATWG URL parser rewrite a request target:
// escapes it resolves or re-encodes, fragment and backslash handling,
// and the characters it percent-encodes in a path. A target containing
// any of them (or a dot segment, or a leading "//" the parser would
// read as an authority) takes the full URL parse below; anything else
// splits into path and query exactly as the parser would report them,
// so the split can be done by hand and no URL object is allocated.
const URL_FALLBACK_CHARS = '%#\\"<>^`{}';

function parseRequestTarget(raw: string): RequestUrl {
  let manual = raw.startsWith('/') && raw[1] !== '/';
  if (manual) {
    for (let i = 0; i < raw.length; i += 1) {
      const code = raw.charCodeAt(i);
      if (code <= 0x20 || code === 0x7f || URL_FALLBACK_CHARS.includes(raw[i])) {
        manual = false;
        break;
      }
    }
  }
  if (manual) {
    const q = raw.indexOf('?');
    const pathname = q === -1 ? raw : raw.slice(0, q);
    for (const segment of pathname.split('/')) {
      if (segment === '.' || segment === '..') {
        manual = false;
        break;
      }
    }
    if (manual) {
      return {
        pathname,
        searchParams: new URLSearchParams(q === -1 ? '' : raw.slice(q + 1)),
      };
    }
  }
  return new URL(raw, 'http://forge.invalid');
}

// The dispatcher's one failure answer: a 500 before anything was sent,
// a bare end once the response is already under way.
function failRequest(res: ServerResponse): void {
  if (!res.headersSent) {
    sendJson(res, 500, { message: 'Internal Server Error' });
  } else {
    res.end();
  }
}

export function createApp(): Server {
  const server = createServer((req, res) => {
    try {
      const url = parseRequestTarget(req.url ?? '/');
      // The path's non-empty segments, decoded: one pass over the
      // split instead of a filter and a map chained behind it.
      const segments: string[] = [];
      for (const rawSegment of url.pathname.split('/')) {
        if (rawSegment.length > 0) segments.push(decodeSegment(rawSegment));
      }
      if (url.pathname === '/healthz' || url.pathname === '/healthz/') {
        sendJson(res, 200, { ok: true });
        return;
      }
      // Git smart HTTP: /<owner>/<repo>.git/<action>, where the action
      // is git-upload-pack, git-receive-pack or the two-segment
      // info/refs.
      const gitAction =
        segments.length === 3 &&
        segments[1].endsWith('.git') &&
        (segments[2] === 'git-upload-pack' || segments[2] === 'git-receive-pack')
          ? segments[2]
          : segments.length === 4 &&
              segments[1].endsWith('.git') &&
              segments[2] === 'info' &&
              segments[3] === 'refs'
            ? 'info/refs'
            : null;
      if (gitAction !== null) {
        const owner = segments[0];
        const repoName = segments[1].slice(0, -'.git'.length);
        if (gitAction === 'info/refs') {
          // Answered without reading a body: run it synchronously
          // instead of through the async handler's promise.
          handleGitInfoRefs(req, res, owner, repoName, url);
        } else {
          void handleGit(req, res, owner, repoName, gitAction, url).catch(() =>
            failRequest(res),
          );
        }
        return;
      }
      if (segments[0] === 'api' && segments[1] === 'v3') {
        if (!requestMayHaveBody(req)) {
          // The common read: no body to wait for, so the handler runs
          // and answers inside this tick, no promise involved.
          handleRest(req, res, segments, url, EMPTY_BODY);
        } else {
          void readBody(req).then(
            (rawBody) => {
              try {
                handleRest(req, res, segments, url, rawBody);
              } catch {
                failRequest(res);
              }
            },
            () => failRequest(res),
          );
        }
        return;
      }
      if (url.pathname === '/api/graphql' || url.pathname === '/api/graphql/') {
        void (async () => {
          try {
            const rawBody = await readBody(req);
            await handleGraphql(req, res, rawBody);
          } catch {
            failRequest(res);
          }
        })();
        return;
      }
      if (url.pathname === '/mcp' || url.pathname === '/mcp/') {
        void (async () => {
          try {
            const rawBody = await readBody(req);
            await handleMcp(req, res, rawBody);
          } catch {
            failRequest(res);
          }
        })();
        return;
      }
      // Drain any request body before answering unknown routes.
      void readBody(req).then(
        () => {
          try {
            notFound(res);
          } catch {
            failRequest(res);
          }
        },
        () => {
          try {
            notFound(res);
          } catch {
            failRequest(res);
          }
        },
      );
    } catch {
      failRequest(res);
    }
  });
  server.keepAliveTimeout = 75000;
  server.headersTimeout = 80000;
  return server;
}
