module

public import Lean
public import VCVioWidgets.GameHop.Model

public section

namespace VCVioWidgets
namespace GameHop

open Lean

/--
Maps modules to the GameHop diagram shown while browsing them.

Keeping these diagrams in widget code lets the panel render from whatever snapshot is already
available, instead of waiting for the current proof file to elaborate a local diagram constant.
-/
structure DiagramBinding where
  modules : Array Name
  diagram : GameDiagram
  deriving Inhabited, Repr

namespace DiagramBinding

def matchesModule (binding : DiagramBinding) (modName : Name) : Bool :=
  binding.modules.contains modName

end DiagramBinding

private def oneTimePadDiagram : GameDiagram := {
  title := "One-time pad: relational hop"
  subtitle := .moduleDoc
  layout := .sequenceWithSideEdges
  mainPath := #["msg0", "msg1", "rows"]
  nodes := #[
    { id := "msg0"
      kind := .game
      title := "Cipher game for msg0"
      anchor? := some (AnchorRef.defn `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp)
      snippets := #[
        .declSource `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp
      ] }
    , { id := "msg1"
        kind := .game
        title := "Cipher game for msg1"
        anchor? := some (AnchorRef.defn `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp)
        snippets := #[
          .text "The same ciphertext experiment, but instantiated with msg1."
            (some (AnchorRef.defn `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp))
        ] }
    , { id := "rows"
        kind := .result
        title := "Equal ciphertext rows"
        anchor? := some (AnchorRef.result `Examples.OneTimePad.oneTimePad.ciphertextRowsEqual)
        snippets := #[
          .declSignature `Examples.OneTimePad.oneTimePad.ciphertextRowsEqual
        ] }
  ]
  edges := #[
    { source := "msg0"
      target := "msg1"
      kind := .equivalence
      label := "GameEquiv"
      detail? := some "Couple keys by the bijection `k ↦ k ⊕ msg0 ⊕ msg1`."
      anchor? := some (AnchorRef.thm `Examples.OneTimePad.oneTimePad.cipherGivenMsg_equiv) }
    , { source := "msg1"
        target := "rows"
        kind := .consequence
        label := "probOutput_eq"
        detail? := some "Turn the equivalence into equality of ciphertext output probabilities."
        anchor? := some (AnchorRef.result `Examples.OneTimePad.oneTimePad.ciphertextRowsEqual)
        notes := #[
          { label := "separate direct proof"
            detail? := some "`perfectSecrecyAt` is proved independently via probability identities."
            anchor? := some (AnchorRef.result `Examples.OneTimePad.oneTimePad.perfectSecrecyAt) }
        ] }
  ]
}

private def elGamalDiagram : GameDiagram := {
  title := "ElGamal IND-CPA via DDH"
  subtitle := .moduleDoc
  layout := .sequenceWithSideEdges
  mainPath := #["game", "hq", "hk1", "hk", "h0", "half", "main"]
  nodes := #[
    { id := "game"
      kind := .game
      title := "IND-CPA game"
      anchor? := some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_game)
      snippets := #[
        .declSource `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_game
      ] }
    , { id := "hq"
        kind := .hybrid
        title := "Hybrid q (all real)"
        anchor? := some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame)
        snippets := #[
          .declSource `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame
        ] }
    , { id := "hk1"
        kind := .hybrid
        title := "Hybrid k + 1"
        anchor? := some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame)
        snippets := #[
          .text "Same hybrid definition as above, instantiated at the next query index."
            (some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame))
        ] }
    , { id := "hk"
        kind := .hybrid
        title := "Hybrid k"
        anchor? := some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame)
        snippets := #[
          .text "The same game family, now viewed at the current hop k."
            (some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame))
        ] }
    , { id := "h0"
        kind := .endpoint
        title := "Hybrid 0 (all random)"
        anchor? := some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame)
        snippets := #[
          .text "The same hybrid family specialized to the fully random endpoint."
            (some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame))
        ] }
    , { id := "half"
        kind := .endpoint
        title := "Winning probability = 1/2"
        anchor? := some (AnchorRef.thm `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_allRandomHalf)
        snippets := #[
          .declSignature `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_allRandomHalf
        ] }
    , { id := "main"
        kind := .result
        title := "Main theorem"
        anchor? := some (AnchorRef.result `Examples.ElGamal.elgamalAsymmEnc.elGamal_IND_CPA_le_q_mul_ddh)
        snippets := #[
          .declSignature `Examples.ElGamal.elgamalAsymmEnc.elGamal_IND_CPA_le_q_mul_ddh
        ] }
  ]
  edges := #[
    { source := "game"
      target := "hq"
      kind := .equality
      label := "bridge to all-real hybrid"
      detail? := some "Bounded-query adversaries see the same distribution in the real game and hybrid `q`."
      anchor? := some (AnchorRef.thm `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridGame_q_eq_game) }
    , { source := "hq"
        target := "hk1"
        kind := .step
        label := "walk down the hybrid family"
        detail? := some "The family is indexed in reverse: `IND_CPA_HybridFamily q i = HybridGame (q - i)`."
        anchor? := some (AnchorRef.defn `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_HybridFamily) }
    , { source := "hk1"
        target := "hk"
        kind := .bound
        label := "|Δ| ≤ 2 * DDH_adv(k)"
        detail? := some "A DDH challenge is embedded into the k-th fresh LR query."
        anchor? := some (AnchorRef.thm `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_stepDDH_hopBound)
        notes := #[
          { label := "reduction"
            detail? := some "The per-hop reduction is `IND_CPA_stepDDHReduction adversary k`."
            anchor? := some (AnchorRef.reduction `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_stepDDHReduction) }
        ] }
    , { source := "hk"
        target := "h0"
        kind := .step
        label := "repeat for the remaining hops"
        detail? := some "The proof sums the absolute differences over all q hops."
        anchor? := some (AnchorRef.result `Examples.ElGamal.elgamalAsymmEnc.elGamal_IND_CPA_bound_toReal) }
    , { source := "h0"
        target := "half"
        kind := .equality
        label := "= 1 / 2"
        detail? := some "Random masking makes the ciphertext distribution independent of the hidden bit."
        anchor? := some (AnchorRef.thm `Examples.ElGamal.elgamalAsymmEnc.IND_CPA_allRandomHalf) }
    , { source := "half"
        target := "main"
        kind := .consequence
        label := "sum hops and plug in ε"
        detail? := some "First prove the summed DDH bound, then collapse each hop to the same `ε`."
        anchor? := some (AnchorRef.result `Examples.ElGamal.elgamalAsymmEnc.elGamal_IND_CPA_le_q_mul_ddh)
        notes := #[
          { label := "summed form"
            detail? := some "The intermediate theorem accumulates the q per-hop DDH bounds."
            anchor? := some (AnchorRef.result `Examples.ElGamal.elgamalAsymmEnc.elGamal_IND_CPA_bound_toReal) }
        ] }
  ]
}

private def bindings : Array DiagramBinding := #[
  { modules := #[`Examples.OneTimePad]
    diagram := oneTimePadDiagram }
  , { modules := #[`Examples.ElGamal]
      diagram := elGamalDiagram }
]

def diagramForModule? (modName : Name) : Option GameDiagram :=
  (bindings.find? (·.matchesModule modName)).map (·.diagram)

end GameHop
end VCVioWidgets
