/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Examples.PRFTagReader.Defs
import Examples.PRFTagReader.Auth
import Examples.PRFTagReader.Collision
import Examples.PRFTagReader.BadEvent

/-!
# PRF Tag/Reader Protocol

This file formalizes a simple RFID-style tag/reader protocol. Each tag is assigned a secret and,
when queried, samples a fresh nonce `n` and outputs `(n, F(secret, n))`. A reader accepts a
transcript `(n, a)` whenever some registered tag secret makes `a` equal to `F(secret, n)`.

The development defines:

- an active authentication game, where the adversary wins by making the reader accept a transcript
  that was not previously emitted by the honest tag oracle;
- a multiple-session unlinkability game, where all sessions of a tag reuse the same per-tag secret;
- a single-session unlinkability game, where each session uses an independent per-session secret;
- an intermediate bad-event world that records nonce collisions across repeated sessions.

The theorem statements package the intended security story: authentication reduces to PRF security
plus an ideal-world argument, and unlinkability reduces to PRF security plus a nonce collision
bound.

The content is split across the `Examples.PRFTagReader.*` modules:

- `Defs`: protocol definitions, game states, oracle specs, experiments;
- `Auth`: the auth→PRF reduction and authentication security
  (`authExp_le_prfAdvantage_add_authRF`, `authIdealExp_eq_zero`,
  `authRFExp_eq_authRFDirectExp`);
- `Collision`: the random-oracle infrastructure and collision-bound theorems;
- `BadEvent`: the bad-event world and the session collision bound.
-/
