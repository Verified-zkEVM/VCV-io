import Lake
open Lake DSL

package VCVio where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.modulesUpperCamelCase, true⟩,
    ⟨`weak.linter.style.whitespace, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.28.0"

/-- Main library. -/
@[default_target] lean_lib VCVio

/-- Shared FFI bindings (SHA-3 / FIPS 202, etc.). -/
lean_lib FFI

/-- Lattice-based cryptography: ring arithmetic, hardness assumptions, and scheme definitions. -/
lean_lib LatticeCrypto

/-- Example constructions of cryptographic primitives. -/
lean_lib Examples
/-- Optional proof widget experiments and visualizations. -/
lean_lib VCVioWidgets
/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib

-- Compile the shared FIPS 202 (SHA-3/SHAKE) FFI wrapper.
-- Uses mlkem-native's FIPS 202 headers for the underlying implementation.
target hashing_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "hashing_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "hashing" / "lean_hashing_ffi.c"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mlkemDir.toString,
    "-I", (mlkemDir / "src").toString,
    "-std=c99", "-O2"]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib leanhashing pkg := do
  let hashO ← hashing_ffi.o.fetch
  let name := nameToStaticLib "leanhashing"
  buildStaticLib (pkg.staticLibDir / name) #[hashO]

-- Compile mlkem-native core and Lean FFI wrappers.
-- Supports multiple parameter sets (512, 768, 1024) via separate TUs.
private def mlkemCFlagsForSet (pkg : NPackage __name__) (paramSet : Nat) :
    FetchM (Array String × Array String) := do
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mlkemDir.toString,
    "-I", (mlkemDir / "src").toString,
    "-DMLK_CONFIG_NO_RANDOMIZED_API",
    s!"-DMLK_CONFIG_PARAMETER_SET={paramSet}",
    "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target mlkem_native.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 768
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mlkem" / "lean_mlkem_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 768
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_native_512.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native_512.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 512
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem512_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem512_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mlkem" / "lean_mlkem512_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 512
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_native_1024.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native_1024.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 1024
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem1024_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem1024_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mlkem" / "lean_mlkem1024_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 1024
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanmlkem pkg := do
  let nativeO ← mlkem_native.o.fetch
  let ffiO ← mlkem_ffi.o.fetch
  let native512 ← mlkem_native_512.o.fetch
  let ffi512 ← mlkem512_ffi.o.fetch
  let native1024 ← mlkem_native_1024.o.fetch
  let ffi1024 ← mlkem1024_ffi.o.fetch
  let name := nameToStaticLib "leanmlkem"
  buildStaticLib (pkg.staticLibDir / name)
    #[nativeO, ffiO, native512, ffi512, native1024, ffi1024]

-- Compile mldsa-native core and Lean FFI wrappers.
-- Supports multiple parameter sets (44, 65, 87) via separate TUs.
private def mldsaCFlagsForSet (pkg : NPackage __name__) (paramSet : Nat) :
    FetchM (Array String × Array String) := do
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mldsaDir.toString,
    "-I", (mldsaDir / "src").toString,
    s!"-DMLD_CONFIG_PARAMETER_SET={paramSet}",
    "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target mldsa_native.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_native.o"
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let srcJob ← inputTextFile <| mldsaDir / "mldsa_native.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 65
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mldsa" / "lean_mldsa_ffi.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 65
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa_native_44.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_native_44.o"
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let srcJob ← inputTextFile <| mldsaDir / "mldsa_native.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 44
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa44_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa44_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mldsa" / "lean_mldsa44_ffi.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 44
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa_native_87.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_native_87.o"
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let srcJob ← inputTextFile <| mldsaDir / "mldsa_native.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 87
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa87_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa87_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mldsa" / "lean_mldsa87_ffi.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 87
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanmldsa pkg := do
  let nativeO ← mldsa_native.o.fetch
  let ffiO ← mldsa_ffi.o.fetch
  let native44 ← mldsa_native_44.o.fetch
  let ffi44 ← mldsa44_ffi.o.fetch
  let native87 ← mldsa_native_87.o.fetch
  let ffi87 ← mldsa87_ffi.o.fetch
  let name := nameToStaticLib "leanmldsa"
  buildStaticLib (pkg.staticLibDir / name)
    #[nativeO, ffiO, native44, ffi44, native87, ffi87]

-- Compile c-fn-dsa (Falcon / FN-DSA) core and Lean FFI wrapper.
private def falconCFlags (pkg : NPackage __name__) :
    FetchM (Array String × Array String) := do
  let fndsaDir := pkg.dir / "third_party" / "c-fn-dsa"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", fndsaDir.toString,
    "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target fndsa.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "fndsa.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "falcon" / "fndsa.c"
  let (weakArgs, traceArgs) ← falconCFlags pkg
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target fndsa_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "fndsa_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "falcon" / "lean_falcon_ffi.c"
  let (weakArgs, traceArgs) ← falconCFlags pkg
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanfalcon pkg := do
  let nativeO ← fndsa.o.fetch
  let ffiO ← fndsa_ffi.o.fetch
  let name := nameToStaticLib "leanfalcon"
  buildStaticLib (pkg.staticLibDir / name) #[nativeO, ffiO]

/-- Test support modules (helpers, vectors). -/
lean_lib VCVioTest

/-- Lattice crypto test support modules (helpers, ACVP vectors). -/
lean_lib LatticeCryptoTest

/-- Smoke test: imports VCVio and prints OK. -/
lean_exe smoke_test where
  root := `VCVioTest.Smoke

/-- ML-KEM test executable (links against mlkem-native FFI). -/
lean_exe mlkem_test where
  root := `LatticeCryptoTest.MLKEM.Main

/-- ML-DSA test executable (links against mldsa-native FFI). -/
lean_exe mldsa_test where
  root := `LatticeCryptoTest.MLDSA.Main

/-- Falcon test executable (links against c-fn-dsa FFI). -/
lean_exe falcon_test where
  root := `LatticeCryptoTest.Falcon.Main
