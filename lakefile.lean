import Lake
open Lake DSL

-- TODO: update linters and remove all errors in library
-- should probably adopt conventions similar to `Batteries`.
abbrev vcvLinters : Array LeanOption := #[
  -- ⟨`linter.docPrime, true⟩,
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.style.cdot, true⟩,
  ⟨`linter.style.dollarSyntax, true⟩,
  ⟨`linter.style.longLine, false⟩, -- temp
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.style.missingEnd, true⟩,
  ⟨`linter.style.setOption, true⟩
]

package VCVio where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]
    ++ vcvLinters.map fun s ↦
      { s with name := `weak ++ s.name }

require "leanprover-community" / "mathlib" @ git "v4.28.0"

/-- Main library. -/
@[default_target] lean_lib VCVio
/-- Example constructions of cryptographic primitives. -/
@[default_target] lean_lib Examples
/-- Optional proof widget experiments and visualizations. -/
lean_lib VCVioWidgets

/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib

-- Compile mlkem-native core and Lean FFI wrapper as separate translation units.
-- Both share the same include paths and config defines.
private def mlkemCFlags (pkg : NPackage __name__) :
    FetchM (Array String × Array String) := do
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mlkemDir.toString,
    "-I", (mlkemDir / "src").toString,
    "-DMLK_CONFIG_NO_RANDOMIZED_API",
    "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target mlkem_native.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlags pkg
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "ffi" / "mlkem" / "lean_mlkem_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlags pkg
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanmlkem pkg := do
  let nativeO ← mlkem_native.o.fetch
  let ffiO ← mlkem_ffi.o.fetch
  let name := nameToStaticLib "leanmlkem"
  buildStaticLib (pkg.staticLibDir / name) #[nativeO, ffiO]

/-- Test support modules (helpers, vectors). -/
lean_lib VCVioTest

/-- Smoke test: imports VCVio and prints OK. -/
lean_exe smoke_test where
  root := `VCVioTest.Smoke

/-- ML-KEM test executable (links against mlkem-native FFI). -/
lean_exe mlkem_test where
  root := `VCVioTest.MLKEM.Main

