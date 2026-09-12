/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction
public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Potential
public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Induction

/-!
# Fischlin Transform: Online Extraction / Knowledge Soundness

Online (straight-line) knowledge soundness for the Fischlin transform: the
extractor `onlineExtract` observes the prover's random-oracle queries, and the
extraction failure probability is bounded via a supermartingale potential
argument, culminating in `knowledgeSoundness`.
-/
