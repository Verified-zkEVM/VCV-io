# References

This file centralizes public external references cited in `README.md`, `docs/agents/`, and the
module docstrings of the Lean libraries. When adding new references to shared docs, prefer
linking here instead of duplicating partial citations inline.

## Papers

### ERHL25

Martin Avanzini, Gilles Barthe, Davide Davoli, and Benjamin Grégoire.
*A Quantitative Probabilistic Relational Hoare Logic*.
In *Proceedings of the 52nd ACM SIGPLAN Symposium on Principles of Programming Languages*
(POPL 2025), Denver, Colorado, USA, January 2025.
DOI: <https://doi.org/10.1145/3704876>
Public abstract and metadata: <https://inria.hal.science/hal-04834149v1>
Preprint: <https://arxiv.org/abs/2407.17127>

Used in:
- `docs/agents/program-logic.md`
- `docs/agents/proof-workflows.md`
- `docs/agents/gotchas.md`

### LOOM26

Vladimir Gladshtein, George Pîrlea, Qiyuan Zhao, Vitaly Kurin, and Ilya Sergey.
*Foundational Multi-Modal Program Verifiers*.
*Proceedings of the ACM on Programming Languages* 10 (POPL), Article 77, January 2026.
DOI: <https://doi.org/10.1145/3776719>

Used in:
- `README.md`

### PRHL14

Gilles Barthe, Cédric Fournet, Benjamin Grégoire, Pierre-Yves Strub, Nikhil Swamy,
and Santiago Zanella-Béguelin.
*Probabilistic Relational Verification for Cryptographic Implementations*.
In *Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages*
(POPL 2014).
DOI: <https://doi.org/10.1145/2535838.2535847>
Public metadata: <https://inria.hal.science/hal-00935743v1>

Background reference for:
- pRHL mentions in `docs/agents/program-logic.md`

### FCF14

Adam Petcher and Greg Morrisett.
*The Foundational Cryptography Framework*.
arXiv:1410.3735, 2014.
DOI: <https://doi.org/10.48550/arXiv.1410.3735>
Public abstract: <https://arxiv.org/abs/1410.3735>

Used in:
- `README.md`

### BDHMS24

Manuel Barbosa, François Dupressoir, Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub.
*A Tight Security Proof for SPHINCS+, Formally Verified*.
Cryptology ePrint Archive, Report 2024/910, 2024.
Preprint: <https://eprint.iacr.org/2024/910>

Used in:
- `docs/design/slh-dsa-fips205-generalization.md`
- `VCVio/CryptoFoundations/TweakableHash.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/Collection.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPREFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTOpenPREFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity/Core.lean`

### DKKW25

Justin Drake, Dmitry Khovratovich, Mikhail Kudinov, and Benedikt Wagner.
*Hash-Based Multi-Signatures for Post-Quantum Ethereum*.
Cryptology ePrint Archive, Report 2025/055, 2025.
Preprint: <https://eprint.iacr.org/2025/055>

Used in:
- `VCVio/CryptoFoundations/TweakableHash.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUD.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUDFinalValidity.lean`

### GHHM21

Alex B. Grilo, Kathrin Hövelmanns, Andreas Hülsing, and Christian Majenz.
*Tight Adaptive Reprogramming in the QROM*.
In *Advances in Cryptology — ASIACRYPT 2021*, Lecture Notes in Computer Science 13090.
DOI: <https://doi.org/10.1007/978-3-030-92062-3_22>
Preprint: <https://eprint.iacr.org/2020/1361>

Used in:
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`

### HK22

Andreas Hülsing and Mikhail Kudinov.
*Recovering the Tight Security Proof of SPHINCS+*.
Cryptology ePrint Archive, Report 2022/346, 2022.
Preprint: <https://eprint.iacr.org/2022/346>

Used in:
- `VCVio/CryptoFoundations/TweakableHash.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/Collection.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPREFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUD.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUDFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity/Core.lean`

## Projects and Repositories

### MATHLIB4

The Lean community.
*mathlib4: The math library of Lean 4*.
GitHub repository: <https://github.com/leanprover-community/mathlib4>
Documentation: <https://leanprover-community.github.io/mathlib4_docs/>

Used in:
- `README.md`

### LOOM-REPO

VERSE Lab.
*loom*.
GitHub repository: <https://github.com/verse-lab/loom>

Used in:
- `README.md`

### FCF-REPO

Adam Petcher.
*fcf*.
GitHub repository: <https://github.com/adampetcher/fcf>

Used in:
- `README.md`

### LEANCRYPTO3-REPO

`dtumad/lean-crypto-formalization`.
Deprecated Lean 3 repository for formalizing cryptography proofs.
GitHub repository: <https://github.com/dtumad/lean-crypto-formalization>

Used in:
- `README.md`
