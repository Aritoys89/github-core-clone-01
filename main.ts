// Entry point for the forge.
//
// The harness launches this file alongside its own environment
// server and expects a small handshake around the real application:
//
//   1. bring the app server up on a port the kernel picks for us,
//   2. tell the environment which port that turned out to be,
//   3. wait until the environment reports the run is finished,
//   4. shut the server down and leave with a success code.
//
// The address of the environment arrives in MAKEFUN_ENV_URL. When
// that variable is missing there is no run to take part in, so we
// refuse to start at all.

import type { Server } from "node:http";
import type { AddressInfo } from "node:net";

import { createApp } from "./app.ts";

// Pause helper used by every retry loop below.
function wait(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// How long to sleep before round `round` of a retry loop: the gap
// starts small, doubles each round, and is capped so a long run
// still polls reasonably often.
function gapFor(round: number): number {
  return Math.min(120 * 2 ** round, 1500);
}

// POST our listening port to the environment. The environment keeps
// whichever registration arrives first, so a 409 answer means the
// slot is already taken and counts as success for us. Anything else
// that goes wrong — a refused connection, a server error — is
// retried with backoff until the registration lands.
async function registerPort(origin: string, port: number): Promise<void> {
  for (let round = 0; ; round++) {
    try {
      const reply = await fetch(new URL("/register", origin), {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ port }),
      });
      if (reply.ok || reply.status === 409) {
        return;
      }
    } catch {
      // The environment may still be starting; fall through to retry.
    }
    await wait(gapFor(round));
  }
}

// Poll the environment's done flag. A failed poll carries no
// information about the run, so errors are treated exactly like a
// "not yet" answer: wait a little and ask again. This only returns
// once the environment says the run is complete.
async function waitUntilDone(origin: string): Promise<void> {
  for (let round = 0; ; round++) {
    try {
      const reply = await fetch(new URL("/done", origin));
      if (reply.ok) {
        const payload = (await reply.json()) as { done?: unknown };
        if (payload.done === true) {
          return;
        }
      }
    } catch {
      // Transient failure; the next round asks again.
    }
    await wait(gapFor(round));
  }
}

async function main(): Promise<void> {
  const origin = process.env.MAKEFUN_ENV_URL;
  if (origin === undefined || origin === "") {
    process.exit(1);
  }

  const server: Server = createApp();

  // Port 0 asks the kernel for a free ephemeral port; 8080 belongs
  // to the environment and is never ours to take.
  await new Promise<void>((resolve) => {
    server.listen(0, () => resolve());
  });
  const bound = server.address() as AddressInfo;

  await registerPort(origin, bound.port);
  await waitUntilDone(origin);

  // The run is over: drop idle keep-alive sockets so close() can
  // finish, wait for the server to wind down, and report success.
  server.closeIdleConnections();
  await new Promise<void>((resolve) => {
    server.close(() => resolve());
  });
  process.exit(0);
}

main().catch(() => {
  process.exit(1);
});
