# 07 — References and Acquisition List

Working bibliography for the suite, split into (a) sources already available locally, (b) papers
to acquire into paper-note (`~/Documents/Research/Papers`), (c) code baselines. PolyFun's
`REFERENCES.md` remains canonical for what its modules cite; this list is the *suite's* reading
map, keyed by direction.

## A. In hand

| Source | Where | Feeds |
|---|---|---|
| Spivak–Niu, *Polynomial Functors* (CUP 2025) + PolyFun ch5–ch8 notes | PolyFun `docs/reading/spivak-niu-ch*.md` | all; ch7–8 → `02`, `06` |
| Libkind–Spivak, *Pattern runs on matter* (EPTCS 429) + note | `docs/reading/pattern-runs-on-matter.md`, arXiv:2404.16321 | `03` |
| Aberlé, *Compositional Program Verification with Polynomial Functors* (Abe26, arXiv 2604.01303) + note | `docs/reading/aberle-parallel.md`; Agda artifact cited therein | `04`, `05` |
| VCVio paper | ePrint 2026/899, PDF in workspace root | all (§10 = paper-3 promise) |
| Canetti, *Universally Composable Security* | Papers: `2000-067` | `06` requirements |
| Canetti et al., UC with a random oracle / global ROs | Papers: `2014-908`, `2018-165` | `05` §2.2 |
| UC-AGM | Papers: `2021-1218` | later (worlds/instrumentation) |
| Strict poly-time simulation/extraction | Papers: `2002-043` | R5 boundary in `06` |
| Hancock–Setzer; Indexed Containers (AGHMM15); ITrees (POPL 2020); Escardó–Oliva | PolyFun `REFERENCES.md` | substrate |
| iris-lean, iris-bluebell, loom2-lean, cslib | workspace checkouts | `04` bridges, `05` kill-criterion comparison, `10` |
| Bao–D'Osualdo–Farzan, *Bluebell* (POPL 2025) | Papers: `Bluebell_Bao_DOsualdo_Farzan_POPL2025_arxiv_2402.18708`; also `iris-bluebell/paper/` | `10` S2 |
| Barthe–Hsu–Liao, *A Probabilistic Separation Logic* (POPL 2020; correction 2026-07-20 — an earlier revision misattributed the third author as Ying) | Papers: `PSL_Barthe_Hsu_Liao_…_arxiv_1907.10708` | `10` §1.1, S2c pilots |
| Li–Ahmed–Holtzen, *Lilac* (PLDI 2023) | Papers: `Lilac_Li_Ahmed_Holtzen_…_arxiv_2304.01339` | `10` (conditioning lineage) |
| Clutch / Eris / Tachis / Foxtrot (Iris-Rocq probabilistic family) | Papers: `Clutch_POPL2024`, `Eris_ICFP2024`, `Tachis_OOPSLA2024`, `Foxtrot_arxiv_2511.10135` | `10` §2 (design sources; tapes = seeded oracle, error credits = bad-event ledger) |
| Blanchet, CryptoVerif corpus: foundational (ePrint 2005/401), long semantics (arXiv 2310.14658), manual v2.12, TLS 1.3 composition (CSF 2018), dynamic compromise (CSF 2024), PQ-sound (CSF 2024), CV2EC (CSF 2024) | Papers: `Blanchet_*`, `cryptoverif-manual-v2.12`, `CryptoVerif_Blanchet_…_arxiv_2310.14658` | `11` §1, `12` Q1 |
| Unruh, *Quantum Relational Hoare Logic* (POPL 2019) + qRHL-FO (ePrint 2020/962); EasyPQC (CCS 2021) | Papers: `Unruh_Quantum_Relational_Hoare_Logic_…`, `Unruh_qRHL_FO_2020`, `EasyPQC_Barthe_2021` | `12` §3 baselines |
| Chiribella–D'Ariano–Perinotti, *Theoretical Framework for Quantum Networks* (PRA 2009) | Papers: `Chiribella_DAriano_Perinotti_…_arxiv_0904.4483` | `12` §3.3 (combs) |
| SSP (ePrint 2018/306), SSProve (TOPLAS 2023), Nominal-SSProve (CSF 2025), CryptHOL-CC (CSF 2019), Broadbent–Karvonen (LMCS 2024), Maurer/Maurer–Renner, IITM (JoC 2020), Canetti 2000/067, GUC (2006/432), Myers book, Libkind Operads/DOTS, Spivak–Niu book + reference | Papers (various; §B items 1–4, 6, 8, 10 of the original list — acquired) | `02`–`06` |

## B. To acquire (priority order; all open-access)

**Status 2026-07-20 (evening): the nine ePrint items below are all acquired and indexed in
paper-note** (Owl 2023/473, OwlC 2025/1092, IPDL 2021/147, Zhandry 2018/276, BDF+11 2010/428,
AHU 2018/904, EasyUC 2019/582, CCL 2014/553, iUC 2019/1073), and the Owl + IPDL artifacts were
inspected at source (`github.com/secure-foundations/owl`, `github.com/ipdl/ipdl`) for the
baseline numbers now cited in `11`. Original items 1–4, 6, 8, 10 were already acquired (§A last
row); item 9 (Nominal-SSProve) likewise. The nine, with their consumers:

1. **Owl** — Gancher–Gibson–Singh–Dharanikota–Parno, ePrint 2023/473 (S&P 2023). `11` §2.
2. **OwlC** — Singh–Gancher–Parno, ePrint 2025/1092 (USENIX Sec 2025). `11` §2.
3. **IPDL** — Morrisett–Shi–Sojakova–Fan–Gancher (author order randomized in publication),
   ePrint 2021/147 (POPL 2023). `11` §2, R-11.2 baseline.
4. **Zhandry, compressed oracles** — ePrint 2018/276 (CRYPTO 2019). `12` §3.3.
5. **BDF+11, Random Oracles in a Quantum World** — ePrint 2010/428 (ASIACRYPT 2011). `12` §1.
6. **Ambainis–Hamburg–Unruh, semi-classical O2H** — ePrint 2018/904 (CRYPTO 2019). `12` R-12.4.
7. **EasyUC** — Canetti–Stoughton–Varia, ePrint 2019/582 (CSF 2019). `06`/`11` baselines.
8. **Canetti–Cohen–Lindell, simpler UC** — ePrint 2014/553. `06` requirements.
9. **iUC** — Camenisch–Krenn–Küsters–Rausch, ePrint 2019/1073. `06` requirements. (Correction
   2026-07-20: an earlier revision of this list cited 2019/1324, which is an unrelated paper.)

Original list (retained for provenance):

1. **Brzuska–Delignat-Lavaud–Fournet–Kohbrok–Kohlweiss, *State-Separating Proofs*** — ePrint
   2018/306. The SSP source of truth; `03` names its reduction lemma as derivation target.
2. **Broadbent–Karvonen, *Categorical composable cryptography*** — arXiv:2105.05949 (+ extended
   FoSSaCS/LMCS version). Attack structures on symmetric monoidal categories; the closest
   published relative of `OpenTheory`+`Emulates`; paper-3 related-work anchor and a check on
   `02`'s ladder placement.
3. **Maurer–Renner, *Abstract Cryptography* / Maurer, *Constructive Cryptography*** (ICS 2011 /
   TOSCA 2011). The resource/converter/distinguisher trinity ↔ `Obj`/`map`/`plug`; the
   "equality up to simulator" algebra `02` §3.4 should be compared against.
4. **Küsters–Tuengerthal(–Rausch), *The IITM Model*** (J. Cryptology 2020 version) and **iUC**
   (ePrint 2019/1073; a prior revision of this doc wrote 2019/1324 — wrong paper). The
   directory/replication discipline `06` adopts; read §on runtime
   accounting for the R5 boundary.
5. **Canetti–Cohen–Lindell, *A simpler variant of UC*** (ePrint 2014/553) and **Canetti–Sarkar–
   Wang JUC/EUC materials** as needed by the `!F_com` pilot's joint-state exclusions.
6. **Myers, *Categorical Systems Theory*** (book draft, davidjaz.com). Doubly indexed functors;
   "behavior of composite = composite of behaviors" — the packaging for `06` §2.4.
7. **EasyUC** (Canetti–Stoughton–Varia, CSF 2019, ePrint 2019/582) and **ILC** (Liao et al.).
   The ≈18k-line baseline every UC rent test is measured against.
8. **Libkind, *Operads for Dynamical Systems* / Libkind–Spivak Org** (arXiv:2112.11518 etc.) —
   mode-dependent wiring for `06` §2.2.
9. **Nominal-SSProve** (LS25 in paper-1's bibliography) — the competing separation mechanism;
   `05`'s frame design should cite its location-quotient approach as the alternative.
10. **Ahman–Uustalu, directed containers / comonoid = category line** — citation hygiene for the
    comonoid layer (PolyFun G0 already lists; mirror into paper-note).

Suggested first action for an implementation agent: `/paper-note` download of items 1–7 with
index entries keyed to this suite's doc numbers.

## C. Code baselines (for honest comparison, not import)

- **SSProve** (Rocq) — package algebra maturity bar for `03`.
- **CryptHOL / Constructive Crypto in CryptHOL** (Isabelle) — the GPV/determinization design
  source the ledger already names for observational equivalence (`02` §3.3 caveat).
- **EasyUC artifact** — routing-cost baseline (`06` honest column).
- **squiggle/aberle Agda artifact** (Abe26) — displayed-parallel executable reference for `04`.
