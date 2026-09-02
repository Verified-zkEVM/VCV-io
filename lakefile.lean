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
    ⟨`weak.linter.style.whitespace, true⟩,
    -- Disable the unicode allowlist linter: VCVio docstrings legitimately use
    -- FIPS-204 math notation (combining tilde `c̃`) and cited author names with
    -- diacritics (e.g. `Cătălin Hriţcu`).
    ⟨`weak.linter.unicodeLinter, false⟩
  ]

/-
Interop backends are intentionally disabled for the Lean 4.33 baseline. Their
source remains under `Interop/`, isolated from the trusted libraries by
`scripts/check-interop-isolation.sh`, but the aggregate module and CI do not
build it. Re-enable a backend only once its upstream Lean library supports the
repository's Lean version without a local compatibility layer.

The pinned Hax revision still targets Lean 4.29.0-rc1 and is not part of the
Lean 4.33 build. Subdirectory: `hax-lib/proof-libs/lean`.
-/
-- require Hax from git
--   "https://github.com/cryspen/hax" @
--   "492a34e3" / "hax-lib/proof-libs/lean"

/-
Loom2 provides the Loom-style WP / Triple program-logic abstractions used in
`VCVio/ProgramLogic/`. Lean 4.33 includes the stable `Std.Do` foundations, but
Loom2's `Std.Do'` layer retains the three-parameter `PredTrans`, `EPost`, and
relational APIs consumed by VCVio. Migrating those clients to the redesigned
`PostShape` API is separate work.

The exact pin below is validated with VCVio's Lean 4.33 baseline.
-/
require loom2 from git
  "https://github.com/quangvdao/loom2" @
  "2f65f311fae959c302586b07aa45390999b935d4"

/-
Aeneas now natively pins Lean and Mathlib v4.31.0. This dormant pin follows its
published `nightly-2026.07.11-15b9684`; keep it disabled until the VCVio bridge
is tested separately and can be enabled without compatibility aliases.
Subdirectory: `backends/lean`.
-/
-- require aeneas from git
--   "https://github.com/AeneasVerif/aeneas" @
--   "15b968482b0dcd7aae45020b6d1bca39b5024af5" / "backends/lean"

/-
List PolyFun before the root Mathlib pin. Lake resolves dependencies in reverse
declaration order, so this keeps the direct Mathlib requirement authoritative
over PolyFun's inherited pin and makes `lake update --keep-toolchain`
idempotent.
-/
require PolyFun from git
  "https://github.com/Verified-zkEVM/PolyFun.git" @
  "c0c923693fc827a41d17116579a0c16ed4873b19"

require "leanprover-community" / "mathlib" @ git "v4.33.1"

/-- Main library. -/
@[default_target] lean_lib VCVio

/-- Native FFI surface: `@[extern]` bindings (SHA-3/SHAKE, ML-KEM, ML-DSA,
Falcon) and every module whose transitive imports reach them. Isolated here so
`VCVio`/`LatticeCrypto` stay link-safe when the `third_party/` native backends
are not checked out. May import `VCVio`/`LatticeCrypto`/`ToMathlib`; nothing in
those libraries may import `Extern`. -/
lean_lib Extern

/-- Lattice-based cryptography: ring arithmetic, hardness assumptions, and scheme definitions. -/
lean_lib LatticeCrypto

/-- Hash-based signatures: SLH-DSA (SPHINCS+, FIPS 205) proof-level specs and security.
Peer of `LatticeCrypto`; may depend on `VCVio`/`ToMathlib` (and Mathlib), but nothing in
`VCVio`/`ToMathlib`/`Extern`/`Interop` may import it. -/
lean_lib HashSig

/-- Example constructions of cryptographic primitives. -/
lean_lib Examples
/-- Optional proof widget experiments and visualizations. -/
lean_lib VCVioWidgets
/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib

/-- Dormant Interop bridges to Rust verification frontends (hax, aeneas).
Strict TCB isolation: no other `lean_lib` may import from `Interop`. See
`Interop/README.md` and `docs/agents/interop.md`. This target is intentionally
excluded from the Lean 4.33 baseline build. -/
lean_lib Interop

/-
The four `extern_lib` targets below compile C sources that live in git
submodules under `third_party/`. Fresh clones do not have those submodules
checked out, and Lake never checks them out for dependencies, yet it links
every `extern_lib` of every transitive dependency into any `lean_exe` it
builds. Each `extern_lib` therefore probes for a source file of its backend
first and falls back to an empty stub archive when the submodule is absent;
linking still succeeds as long as the executable does not reference the
native FFI symbols. Run `git submodule update --init --recursive` to enable
the real backends.
-/

/-- `true` if `marker` — a file that one of the native-backend `.o` targets
reads from a `third_party/` submodule — exists in this checkout. -/
private def nativeSrcPresent (pkg : NPackage __name__)
    (marker : System.FilePath) : FetchM Bool := do
  (pkg.dir / marker).pathExists

/-- Build an empty stub archive for `libName`, logging that the native backend
from `submodule` is disabled. A missing submodule is the expected state when
VCVio is built as a dependency (`logInfo`) but usually an oversight when
building in-repo (`logWarning`). -/
private def buildNativeStub (pkg : NPackage __name__)
    (libName submodule : String) : FetchM (Job System.FilePath) := do
  let msg := s!"{libName}: native backend disabled because '{submodule}' is \
not checked out; building an empty stub archive instead. Executables still \
link unless they reference VCVio's native FFI symbols. To enable the \
backend, run `git submodule update --init --recursive` in '{pkg.dir}' and \
rebuild."
  if pkg.isRoot then logWarning msg else logInfo msg
  buildStaticLib (pkg.staticLibDir / nameToStaticLib libName) #[]

/-- `third_party/mlkem-native` marker for `leanhashing`: the FIPS 202 header
included by `csrc/hashing/lean_hashing_ffi.c`. -/
private def mlkemFips202Header : System.FilePath :=
  "third_party" / "mlkem-native" / "mlkem" / "src" / "fips202" / "fips202.h"

/-- `third_party/mlkem-native` marker for `leanmlkem`: the amalgamated source
compiled by the `mlkem_native*.o` targets. -/
private def mlkemNativeSrc : System.FilePath :=
  "third_party" / "mlkem-native" / "mlkem" / "mlkem_native.c"

/-- `third_party/mldsa-native` marker for `leanmldsa`: the amalgamated source
compiled by the `mldsa_native*.o` targets. -/
private def mldsaNativeSrc : System.FilePath :=
  "third_party" / "mldsa-native" / "mldsa" / "mldsa_native.c"

/-- `third_party/c-fn-dsa` marker for `leanfalcon`: the API header included by
`csrc/falcon/lean_falcon_ffi.c`. -/
private def fndsaHeader : System.FilePath :=
  "third_party" / "c-fn-dsa" / "fndsa.h"

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
  if ← nativeSrcPresent pkg mlkemFips202Header then
    let hashO ← hashing_ffi.o.fetch
    let name := nameToStaticLib "leanhashing"
    buildStaticLib (pkg.staticLibDir / name) #[hashO]
  else
    buildNativeStub pkg "leanhashing" "third_party/mlkem-native"

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
  if ← nativeSrcPresent pkg mlkemNativeSrc then
    let nativeO ← mlkem_native.o.fetch
    let ffiO ← mlkem_ffi.o.fetch
    let native512 ← mlkem_native_512.o.fetch
    let ffi512 ← mlkem512_ffi.o.fetch
    let native1024 ← mlkem_native_1024.o.fetch
    let ffi1024 ← mlkem1024_ffi.o.fetch
    let name := nameToStaticLib "leanmlkem"
    buildStaticLib (pkg.staticLibDir / name)
      #[nativeO, ffiO, native512, ffi512, native1024, ffi1024]
  else
    buildNativeStub pkg "leanmlkem" "third_party/mlkem-native"

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
    -- Exclude the randomized signing API (mirrors mlkem's `MLK_CONFIG_NO_RANDOMIZED_API`):
    -- it pulls in an undefined `randombytes` symbol that fails to link on Linux, and the
    -- FFI tests only exercise the internal deterministic API.
    "-DMLD_CONFIG_NO_RANDOMIZED_API",
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
  if ← nativeSrcPresent pkg mldsaNativeSrc then
    let nativeO ← mldsa_native.o.fetch
    let ffiO ← mldsa_ffi.o.fetch
    let native44 ← mldsa_native_44.o.fetch
    let ffi44 ← mldsa44_ffi.o.fetch
    let native87 ← mldsa_native_87.o.fetch
    let ffi87 ← mldsa87_ffi.o.fetch
    let name := nameToStaticLib "leanmldsa"
    buildStaticLib (pkg.staticLibDir / name)
      #[nativeO, ffiO, native44, ffi44, native87, ffi87]
  else
    buildNativeStub pkg "leanmldsa" "third_party/mldsa-native"

-- Compile c-fn-dsa (Falcon / FN-DSA) core and Lean FFI wrapper.
private def falconCFlags (pkg : NPackage __name__) :
    FetchM (Array String × Array String) := do
  let fndsaDir := pkg.dir / "third_party" / "c-fn-dsa"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", fndsaDir.toString,
    -- `_GNU_SOURCE` is required on glibc: under `-std=c99` it otherwise hides
    -- `getentropy` / `O_CLOEXEC`, which `third_party/c-fn-dsa/sysrng.c` uses, so
    -- the Falcon RNG fails to compile on Linux (macOS exposes them regardless).
    "-D_GNU_SOURCE", "-std=c99", "-O2"]
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
  if ← nativeSrcPresent pkg fndsaHeader then
    let nativeO ← fndsa.o.fetch
    let ffiO ← fndsa_ffi.o.fetch
    let name := nameToStaticLib "leanfalcon"
    buildStaticLib (pkg.staticLibDir / name) #[nativeO, ffiO]
  else
    buildNativeStub pkg "leanfalcon" "third_party/c-fn-dsa"

/-- Test support modules (helpers, vectors). -/
lean_lib VCVioTest

/-- Lattice crypto test support modules (helpers, ACVP vectors). -/
lean_lib LatticeCryptoTest

/-- SLH-DSA known-answer test executables (differential tests vs external reference signers).
Test-only and deliberately kept out of the `HashSig` library aggregate: each KAT module carries a
root-level `main`, and a `submodules` glob builds them independently so the entry points never
collide. -/
lean_lib HashSigTest where
  globs := #[.submodules `HashSigTest]

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

/-- SLH-DSA-SHA2-128-24 known-answer test: pure-Lean concrete verify vs the C reference vector. -/
lean_exe slhdsa_kat where
  root := `HashSigTest.SLHDSA.Sha2KAT

/-- C13 known-answer test: pure-Lean keccak256 concrete verify vs the reference signer vector. -/
lean_exe slhdsa_c13_kat where
  root := `HashSigTest.SLHDSA.C13KAT

/-- Exact parameter-width and structured key/signature wire-codec regression suite. -/
lean_exe slhdsa_data_codec_tests where
  root := `HashSigTest.SLHDSA.DataCodecTests

/-- SHA2/SHAKE vectors, address rejection, and all-profile primitive grammars. -/
lean_exe slhdsa_primitive_tests where
  root := `HashSigTest.SLHDSA.PrimitiveTests

/-- WOTS+ checksum/construction exercise across all approved SHA2/SHAKE profiles. -/
lean_exe slhdsa_wots_tests where
  root := `HashSigTest.SLHDSA.WotsConstructionTests

/-- Bounded XMSS construction, address-domain, and selected concrete-profile exercise. -/
lean_exe slhdsa_xmss_tests where
  root := `HashSigTest.SLHDSA.XmssConstructionTests

/-- S07 FORS extraction, address-domain, tiny exhaustion, and selected concrete-profile exercise. -/
lean_exe slhdsa_fors_tests where
  root := `HashSigTest.SLHDSA.ForsConstructionTests

/-- General-hypertree trajectories, checked addresses, and selected concrete construction. -/
lean_exe slhdsa_hypertree_tests where
  root := `HashSigTest.SLHDSA.HypertreeConformanceTests

/-- Algorithms 21--25 message boundary and all twelve ACVP pre-hash digest/OID canaries. -/
lean_exe slhdsa_external_tests where
  root := `HashSigTest.SLHDSA.External

lean_exe slhdsa_target_ledger_tests where
  root := `HashSigTest.SLHDSA.ReachableTargets

/-- Kernel-level axiom / `sorry` accounting across the non-test libraries, with a
committed regression baseline (`scripts/axiom_baseline.json`). Complements the Interop
TCB-isolation gate: that gate bounds imports, this one accounts for the axioms every
declaration ultimately rests on. Runtime-imports built oleans, so run it after
`lake build`. See `scripts/AxiomSweep.lean`. -/
lean_exe axiomsweep where
  srcDir := "scripts"
  root := `AxiomSweep
  supportInterpreter := true

/-- Isolated fixtures for the axiom-sweep mutation matrix, exercised by
`scripts/test-axiomsweep.sh`. Not a default target, and deliberately carrying synthetic
kernel taint: `sorryAx` reached directly and transitively, an axiom occurring only in a
type, a mutual-inductive family whose taint crosses the cycle, and names that imitate the
generated `._native.` suffix. Kept out of every aggregate so the taint stays quarantined
from the swept libraries. -/
lean_lib VCVioAxiomSweepTestFixtures where
  srcDir := "scripts"
  globs := #[.submodules `VCVioAxiomSweepTestFixtures]
