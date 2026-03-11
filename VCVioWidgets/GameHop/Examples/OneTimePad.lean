module

public import VCVioWidgets.GameHop.Model

public section

namespace VCVioWidgets
namespace GameHop
namespace Examples
namespace OneTimePad

open Lean
open VCVioWidgets.GameHop

private def dotted (parts : List String) : Name :=
  parts.foldl Name.str Name.anonymous

private def perfectSecrecyCipherGivenMsgExp : Name :=
  dotted ["SymmEncAlg", "PerfectSecrecyCipherGivenMsgExp"]

private def otpCipherGivenMsgEquiv : Name :=
  dotted ["oneTimePad", "cipherGivenMsg_equiv"]

private def otpCiphertextRowsEqual : Name :=
  dotted ["oneTimePad", "ciphertextRowsEqual"]

private def otpPerfectSecrecyAt : Name :=
  dotted ["oneTimePad", "perfectSecrecyAt"]

def cipherGivenMsgEquivDiagram : VCVioWidgets.GameHop.GameDiagram :=
  { title := "One-time pad: relational hop"
    subtitle? := some
      "This diagram follows the relational proof around `cipherGivenMsg_equiv` and its\n\
       `probOutput_eq` corollary. The final theorem `perfectSecrecyAt` in the file is proved\n\
       separately by direct probability calculations, so the widget keeps that distinction explicit."
    layout := .sequenceWithSideEdges
    mainPath := #["msg0", "msg1", "rows"]
    nodes := #[
      { id := "msg0"
        kind := .game
        title := "Cipher game for msg₀"
        summary := "Sample a fresh OTP key and encrypt the fixed message `msg₀`."
        anchor? := some (AnchorRef.defn perfectSecrecyCipherGivenMsgExp)
        snippets := #[
          .text "oneTimePad.PerfectSecrecyCipherGivenMsgExp sp msg₀"
            (some (AnchorRef.defn perfectSecrecyCipherGivenMsgExp))
        ] }
      , { id := "msg1"
          kind := .game
          title := "Cipher game for msg₁"
          summary := "Run the same experiment with `msg₁`; OTP symmetry makes the ciphertext law match."
          anchor? := some (AnchorRef.defn perfectSecrecyCipherGivenMsgExp)
          snippets := #[
            .text "oneTimePad.PerfectSecrecyCipherGivenMsgExp sp msg₁"
              (some (AnchorRef.defn perfectSecrecyCipherGivenMsgExp))
          ] }
      , { id := "rows"
          kind := .result
          title := "Equal ciphertext rows"
          summary := "The relational equivalence yields equal ciphertext probabilities for every pair of messages."
          anchor? := some (AnchorRef.result otpCiphertextRowsEqual)
          snippets := #[
            .declType otpCiphertextRowsEqual
          ] }
    ]
    edges := #[
      { source := "msg0"
        target := "msg1"
        kind := .equivalence
        label := "GameEquiv"
        detail? := some "Couple keys by the bijection `k ↦ k ⊕ msg₀ ⊕ msg₁`."
        anchor? := some (AnchorRef.thm otpCipherGivenMsgEquiv) }
      , { source := "msg1"
          target := "rows"
          kind := .consequence
          label := "probOutput_eq"
          detail? := some "Turn the equivalence into equality of ciphertext output probabilities."
          anchor? := some (AnchorRef.result otpCiphertextRowsEqual)
          notes := #[
            { label := "separate direct proof"
              detail? := some "`perfectSecrecyAt` is proved independently via probability identities."
              anchor? := some (AnchorRef.result otpPerfectSecrecyAt) }
          ] }
    ] }

end OneTimePad
end Examples
end GameHop
end VCVioWidgets
