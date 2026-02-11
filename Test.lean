import VCVio
-- import LibSodium

-- Roll a bunch of dice at random.
private def lawLargeNumsTest (trials : ℕ) (die : ℕ) : IO Unit := do
  let n : ℕ := trials * die
  let xs ← OracleComp.replicateTR n $[0..die - 1]
  IO.println ("Rolling " ++ toString n ++ " " ++ toString die ++ "-sided dice:")
  for i in List.range die do
    IO.println <| "▸Num " ++ toString (i + 1) ++ "s: " ++ toString (xs.count i)

-- dtumad: this requires precompiles of mathlib which is very slow right now
-- def main : IO Unit := do
--   IO.println <| "Thanks for running me!"
--   IO.println <| "Running an external addition of `1 + 1`:"
--   IO.println <| myAdd 1 1
--   IO.println <| "----------------------------------------"
--   let trials : ℕ ← (100 + ·) <$> $[0..100]
--   let die : ℕ ← (4 + ·) <$> $[0..4]
--   lawLargeNumsTest trials die
