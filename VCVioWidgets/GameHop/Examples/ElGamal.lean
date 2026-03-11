module

public import VCVioWidgets.GameHop.Model

public section

namespace VCVioWidgets
namespace GameHop
namespace Examples
namespace ElGamal

open Lean
open VCVioWidgets.GameHop

private def dotted (parts : List String) : Name :=
  parts.foldl Name.str Name.anonymous

private def indCpaGame : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_game"]

private def hybridGame : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_HybridGame"]

private def hybridFamily : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_HybridFamily"]

private def allRandomHalf : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_allRandomHalf"]

private def stepReduction : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_stepDDHReduction"]

private def hopBound : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_stepDDH_hopBound"]

private def hybridQEqGame : Name :=
  dotted ["elgamalAsymmEnc", "IND_CPA_HybridGame_q_eq_game"]

private def summedBound : Name :=
  dotted ["elgamalAsymmEnc", "elGamal_IND_CPA_bound_toReal"]

private def finalTheorem : Name :=
  dotted ["elgamalAsymmEnc", "elGamal_IND_CPA_le_q_mul_ddh"]

def hybridSequenceDiagram : VCVioWidgets.GameHop.GameDiagram :=
  { title := "ElGamal IND-CPA via DDH"
    subtitle? := some
      "The file proves a q-step hybrid argument. This widget shows the bridge from the real game\n\
       to the all-real hybrid, one representative DDH hop, the all-random endpoint, and the final\n\
       collapse to `q * (2 * ε)`."
    layout := .sequenceWithSideEdges
    mainPath := #["game", "hq", "hk1", "hk", "h0", "half", "main"]
    nodes := #[
      { id := "game"
        kind := .game
        title := "IND-CPA game"
        summary := "The actual ElGamal IND-CPA experiment against the adversary."
        anchor? := some (AnchorRef.defn indCpaGame)
        snippets := #[
          .text "elgamalAsymmEnc.IND_CPA_game adversary"
            (some (AnchorRef.defn indCpaGame))
        ] }
      , { id := "hq"
          kind := .hybrid
          title := "Hybrid q (all real)"
          summary := "Every fresh LR query is answered by real ElGamal encryption."
          anchor? := some (AnchorRef.defn hybridGame)
          snippets := #[
            .text "IND_CPA_HybridGame adversary q"
              (some (AnchorRef.defn hybridGame))
          ] }
      , { id := "hk1"
          kind := .hybrid
          title := "Hybrid k + 1"
          summary := "The first `k + 1` fresh LR queries are real; the rest are random-masked."
          anchor? := some (AnchorRef.defn hybridGame)
          snippets := #[
            .text "IND_CPA_HybridGame adversary (k + 1)"
              (some (AnchorRef.defn hybridGame))
          ] }
      , { id := "hk"
          kind := .hybrid
          title := "Hybrid k"
          summary := "The k-th fresh query has already been replaced by the random-masked variant."
          anchor? := some (AnchorRef.defn hybridGame)
          snippets := #[
            .text "IND_CPA_HybridGame adversary k"
              (some (AnchorRef.defn hybridGame))
          ] }
      , { id := "h0"
          kind := .endpoint
          title := "Hybrid 0 (all random)"
          summary := "Every fresh LR query uses `randomMaskedCipher`, so the challenge bit is hidden."
          anchor? := some (AnchorRef.defn hybridGame)
          snippets := #[
            .text "IND_CPA_HybridGame adversary 0"
              (some (AnchorRef.defn hybridGame))
          ] }
      , { id := "half"
          kind := .endpoint
          title := "Winning probability = 1/2"
          summary := "The all-random endpoint is independent of the challenge bit."
          anchor? := some (AnchorRef.thm allRandomHalf)
          snippets := #[
            .declType allRandomHalf
          ] }
      , { id := "main"
          kind := .result
          title := "Main theorem"
          summary := "If every hop is bounded by `ε`, the total IND-CPA advantage is at most `q * (2 * ε)`."
          anchor? := some (AnchorRef.result finalTheorem)
          snippets := #[
            .declType finalTheorem
          ] }
    ]
    edges := #[
      { source := "game"
        target := "hq"
        kind := .equality
        label := "bridge to all-real hybrid"
        detail? := some "Bounded-query adversaries see the same distribution in the real game and hybrid `q`."
        anchor? := some (AnchorRef.thm hybridQEqGame) }
      , { source := "hq"
          target := "hk1"
          kind := .step
          label := "walk down the hybrid family"
          detail? := some "The family is indexed in reverse: `IND_CPA_HybridFamily q i = HybridGame (q - i)`."
          anchor? := some (AnchorRef.defn hybridFamily) }
      , { source := "hk1"
          target := "hk"
          kind := .bound
          label := "|Δ| ≤ 2 * DDH_adv(k)"
          detail? := some "A DDH challenge is embedded into the k-th fresh LR query."
          anchor? := some (AnchorRef.thm hopBound)
          notes := #[
            { label := "reduction"
              detail? := some "The per-hop reduction is `IND_CPA_stepDDHReduction adversary k`."
              anchor? := some (AnchorRef.reduction stepReduction) }
          ] }
      , { source := "hk"
          target := "h0"
          kind := .step
          label := "repeat for the remaining hops"
          detail? := some "The proof sums the absolute differences over all q hops."
          anchor? := some (AnchorRef.result summedBound) }
      , { source := "h0"
          target := "half"
          kind := .equality
          label := "= 1 / 2"
          detail? := some "Random masking makes the ciphertext distribution independent of the hidden bit."
          anchor? := some (AnchorRef.thm allRandomHalf) }
      , { source := "half"
          target := "main"
          kind := .consequence
          label := "sum hops and plug in ε"
          detail? := some "First prove the summed DDH bound, then collapse each hop to the same `ε`."
          anchor? := some (AnchorRef.result finalTheorem)
          notes := #[
            { label := "summed form"
              detail? := some "The intermediate theorem accumulates the q per-hop DDH bounds."
              anchor? := some (AnchorRef.result summedBound) }
          ] }
    ] }

end ElGamal
end Examples
end GameHop
end VCVioWidgets
