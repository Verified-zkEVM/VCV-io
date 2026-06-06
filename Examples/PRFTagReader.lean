/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

import Examples.PRFTagReader.Defs
import Examples.PRFTagReader.BadEvent
import Examples.PRFTagReader.Auth
import Examples.PRFTagReader.Collision
import Examples.PRFTagReader.UnlinkReduction

/-!
# PRF Tag/Reader Protocol

Formalization of a simple RFID-style tag/reader protocol. Each tag holds a secret and, on query,
samples a fresh nonce `n` and outputs `(n, F(secret, n))`. A reader accepts a transcript `(n, a)`
whenever some registered tag secret makes `a` equal to `F(secret, n)`.

Main security statements:

- active authentication: the adversary wins by making the reader accept a transcript not previously
  emitted by the honest tag oracle;
- multiple-session unlinkability: all sessions of a tag share a single per-tag secret;
- single-session unlinkability: each session uses an independent fresh secret;
- a bad-event world tracking nonce collisions across repeated sessions, bridging the two
  unlinkability games via PRF security plus a collision bound.

Content is split across `Examples.PRFTagReader.Defs` (protocol, games, oracle specs),
`Examples.PRFTagReader.BadEvent` (bad-event world used by the unlinkability reduction),
`Examples.PRFTagReader.Auth` (authentication PRF reduction), and
`Examples.PRFTagReader.Collision` (random-function authentication collision bound, distinct-nonce
regime).
-/
