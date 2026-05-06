# Formal vs informal notes

## extractability_game_no_coll_match

The blueprint outline says "extractor produces the same tree whether built
from `committingLog` or from `log` — any new entries in `log` with response
equal to an existing one would be a collision". This is stronger than what
actually holds: the trees only agree along the intact path, not globally
(off-path values reached during `populate_down` may have `log_c.find?` empty
but `log.find?` non-empty, in which case the trees disagree at that subtree).

The Lean proof therefore avoids claiming global tree equality. Instead it
restricts the chain to `log_c` via `chainInLog_restrict` and applies
`extractor_chain_match` on `log_c` directly. This delivers the exact
conclusion the bundled lemma needs without going through tree equality.
