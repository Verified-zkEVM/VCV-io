
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace hax_cbd

--  One centered-binomial coefficient at parameter η = 1.
-- 
--  The two low bits of `b` are treated as independent Bernoulli(1/2)
--  samples `a`, `c`; the output is `a − c`. All six higher bits of
--  `b` are unused by this function.
@[spec]
def sample_cbd1 (b : u8) : RustM i32 := do
  let a : i32 ← (rust_primitives.hax.cast_op (← (b &&&? (1 : u8))) : RustM i32);
  let c : i32 ←
    (rust_primitives.hax.cast_op
      (← ((← (b >>>? (1 : i32))) &&&? (1 : u8))) :
      RustM i32);
  (a -? c)

end hax_cbd

