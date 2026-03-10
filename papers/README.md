# Reference Papers

These papers are downloaded for local agent reference. **Never commit this folder.**

## Papers

| File | Title | Venue | Relevance |
|------|-------|-------|-----------|
| `eRHL_POPL2025.pdf` | A Quantitative Probabilistic Relational Hoare Logic | POPL 2025 | **Primary design target** for VCV-io relational logic. ℝ≥0∞-valued pre/post, subsumes pRHL+apRHL. |
| `Loom_POPL2026.pdf` | Foundational Multi-Modal Program Verifiers | POPL 2026 | Source of `MAlgOrdered` / monad algebra WP architecture already ported to VCV-io. |
| `pRHL_Barthe_2009.pdf` | Probabilistic Relational Verification for Cryptographic Implementations | 2009 | Original pRHL — exact coupling semantics. Current `RelTriple` implements this. |
| `apRHL_diff_privacy_Barthe_2012.pdf` | Probabilistic Relational Reasoning via Metrics | 2012 | apRHL — ε-approximate couplings for differential privacy. |
| `Approxis_apRHL_higher_order.pdf` | Approximate Relational Reasoning for Higher-Order Probabilistic Programs | 2024 | Higher-order apRHL in Iris/Coq. Error credits approach. |
| `EasyCrypt_Barthe_2011.pdf` | Computer-Aided Security Proofs for the Working Cryptographer | 2020 | EasyCrypt reference — `proc`, `rnd`, `swap` tactics, module system. |
| `SSProve_2021.pdf` | SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq | 2021 | State-separating proofs, package algebra for modular reductions. |
| `CryptoHOL_2017.pdf` | CryptHOL | 2017 | Isabelle/HOL crypto framework. Free-monad GPVs (similar to OracleComp). |
| `FCF_Petcher_Morrisett_2015.pdf` | The Foundational Cryptography Framework | 2015 | Coq crypto framework. Game-hopping tactics. |
| `Bellare_Rogaway_GamePlaying_2006.pdf` | The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs | 2006 | "Identical until bad" / fundamental lemma of game playing. |
