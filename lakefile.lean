import Lake
open Lake DSL

abbrev vcvLinters : Array LeanOption := #[
  -- ⟨`linter.docPrime, true⟩,
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.style.cdot, true⟩,
  ⟨`linter.style.dollarSyntax, true⟩,
  -- ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.style.longLine, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.style.missingEnd, true⟩,
  ⟨`linter.style.setOption, true⟩
]

package VCVio where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, true⟩]
    ++ vcvLinters.map fun s ↦
      { s with name := `weak ++ s.name }

require "leanprover-community" / "mathlib" @ git "v4.24.0"

require iris from git "https://github.com/leanprover-community/iris-lean" @ "36d042d249311727eb87acbef36b9d401bf44450"

/-- Main library. -/
@[default_target] lean_lib VCVio
/-- Example constructions of cryptographic primitives. -/
@[default_target] lean_lib Examples

/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib
/-- Access to external C++ implementations of crypto primitives. -/
lean_lib LibSodium

/-- Main function for testing -/
lean_exe test where root := `Test

-- /-- Runnable implementations of specific cryptographic algorithms.
-- Set `precompileModules` in order to allow execution of external code. -/
-- lean_lib Implementations where
--    precompileModules := true

-- Compiling extenal C++ files
target libsodium.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "libsodium.o"
  let srcJob ← inputTextFile <| pkg.dir / "LibSodium" / "c" / "libsodium.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace
extern_lib libleanffi pkg := do
  let ffiO ← libsodium.o.fetch
  let name := nameToStaticLib "leanlibsodium"
  buildStaticLib (pkg.sharedLibDir / name) #[ffiO]
