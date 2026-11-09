# Independent adversarial review: MathDB 337352 (riordan-diameter-review-r1)

Reviewer: Claude (claude-opus-5-5), lane `new-twenty-2026-10-31/riordan-diameter-review-r1`, 2026-11-04 UTC.

This is a review, not an acceptance. Credit is zero and root decides. The review used no child agents and no git,
and it touched no ledger. Lean, lake, leanchecker and SAT/ILP solvers were not run. Only capped `python3 -I`
processes were used, one at a time. The unrelated `riordan-review-r1` lane was not touched.

**Candidate.** Discovery lane `expanded-corpus-r146` (Claude) claims to resolve CJKM *Riordan graphs I*,
Conjecture 2. Its theorem: for every k ≥ 4, an io-decomposable Bell-type G_{2^k} with diameter k equals CG_{2^k}.
Two readings follow:

* the family reading (R2) holds;
* the per-k reading (R1) holds exactly for k = 1 and k ≥ 4.

## Verdicts

| Gate | Verdict | One-line reason |
|---|---|---|
| A Statement fidelity | **QUALIFIED_PASS** | (R2) is the intended reading (strong textual evidence, §A.2). (R1) is literally false at k = 2 by CJKM's own Thm 4.22, and at k = 3. The lane's "Table 1 typo" correction is wrong. The io class must be the Thm 4.6 A-sequence class. |
| B Independent mathematics | **PASS** | All lemmas re-derived. All published facts located and verified. Every finite claim reproduced with my own code. Two lane overstatements are corrected (Lemma A is not new; the k = 4 base is Jung's Thm 3.3 at k = 4). |
| C Lean route | **QUALIFIED_PASS** | The draft's architecture is sound but expensive. A cheaper Lagrange-free route proves (R2) without general P1, P2, P5 or Lagrange inversion: MEDIUM, about 1,600–3,100 lines (`LEAN-ROUTE.md`). The per-k endpoint stays HIGH. |
| D Prior art | **QUALIFIED_PASS** | OpenAlex shows Jung is cited by 2 works and CJKM I by 13. Neither group, nor Jung's later papers, resolves Conjecture 2. This is a bounded search. Lemma A's formula is in the source itself (CJKM Thm 3.14 / Jung Lemma 2.3). |
| E Significance and exclusion | **QUALIFIED (borderline)** | It fully resolves the intended statement of a conjecture the source's own author resolved only partially in a 2022 journal paper. But almost all of it is the authors' own machinery; the genuinely new content is a 4-line power-series lemma (Lemma B). Root must choose between the 372205 and 347138 lines. |
| **Overall** | **HOLD** | The mathematics is correct. Do not start Lean until root rules on E. If root rules it eligible, **PROCEED with endpoint E1 (R2 plus both clauses) via the Lagrange-free route**, plus the zero-credit literal negation E0. |

---

## Inputs and hash binding

* Discovery lane `../expanded-corpus-r146`: all 195 files were hashed before and after the review
  (`hashes/inputs-before.sha256` and `hashes/inputs-after.sha256`).
  * The two lists are byte-identical. sha256 of each list: `4612c4388cee8d37216e8b23803a548da1904001570bad4e822c44998a7ec7c1`.
  * Key files:
    * `outputs/337352-proof.md` 2b39d557…
    * `lean/Riordan337352.lean` 2b7aa767…
    * `SUMMARY.md` 871ae46b…
    * `results.json` 0dcd858f…
    * `extracted.json` 452a65c2…
    * `raw/337352.jsonl` 40cae49f…
* MathDB record: I re-hashed corpus chunk `mathdb-normalized-chunk-0005.jsonl`, line 1774.
  * chunk sha256 026158d6…: matches;
  * raw line sha256 40cae49f…: matches;
  * statement sha256 d8100314…: matches.
  * Its `references` field says "Status: **refuted** according to the source (as of October 2017)". This is a
    MathDB metadata artefact: v2 says Conjecture **1** was refuted, while Conjecture 2 is posed as open in both v1
    and v2. It is not evidence about Conjecture 2.
* Sources: I fetched these myself into the fresh lane directory `dl/`, with TLS verification on, all HTTP 200
  (`logs/fetch-arxiv.log`):
  * arXiv abs 1710.04604 and 1901.11156;
  * PDF 1710.04604v1, v2 and 1901.11156 (v1, the only version).

  All are **byte-identical** to the lane's copies (sha256 301b7b01…, 5aa1e837…, e5fdc2bb…, 1ebf9ead…, 0758db97…).
  I extracted the text myself (`text/`, pdftotext -layout). Jung p. 12 was rendered to `render/jung-p12-12.png`
  for the tables.
* Line references below are to my extractions:
  * `text/pdf_1901.11156.txt` (J);
  * `text/pdf_1710.04604v2.txt` (C2);
  * `text/pdf_1710.04604v1.txt` (C1).

---

## A. Statement fidelity: QUALIFIED_PASS

### A.1 Source definitions (all confirmed)

* **Riordan graph.**
  * C2:476–487, Def. 2.4: A(G) = B + Bᵀ with B = B(tg, f)_n.
  * C2:491–494, eq. (4): for i > j ≥ 1, a_{ij} ≡ [t^{i−2}] g f^{j−1} = r_{i−2, j−1}.
  * The same in J:67–75 (Def. 1.1).
  * For f = zg this is i ~ j iff [z^{i−1}] f^j = 1, as the lane states (proof.md:53–54).
  * Note: v1's "Definition 2.4" is the infinite graph (C1:272). The finite definition sits elsewhere in v1. The
    brief's numbering matches v2.
* **Bell matrix recurrence.**
  * J:512–521, eq. (9): b_{i+1,0} = Σ a_{t+1} b_{i,t} and b_{i+1,j+1} = b_{i,j} + Σ_{t≥1} a_t b_{i,j+t}.
  * "We need the finite term (1, a_1, …, a_{n−2}) … to determine A(G_n)" (J:520–521).
  * My construction from (9) agrees with the independent power-series construction from eq. (4) on all 811 tested
    graphs. It reproduces the printed A(CG_6) (C2 Example 2.5; J Fig. 1) and Jung's printed A(CG^r_8) (J:342–355)
    (`logs/s1_construct.log`).
* **Bell type** f = zg (J:89).
* **io-decomposable.**
  * Definition: C2:1880–1885 and J:92–96.
  * A-sequence characterisation (1, 1, a_2, a_2, a_4, a_4, …): C2:1975–1991 Thm 4.6 = C1:1417 = J:168–170
    Lemma 2.1.
* **Catalan graph** CG_n = G_n(C, zC), with A-sequence 1/(1−z), i.e. all ones (C2 Ex. 4.8).
* **Diameter**: C2:2189–2191, Def. 4.21.

### A.2 Which reading of "for all k ≥ 1"

Conjecture 2 (C2:2354–2356, C1:1814–1816, quoted at J:137–138) reads: "diam(CG_{2^k}) = k and there are no
io-decomposable Riordan graphs G_{2^k} ≇ CG_{2^k} of the Bell type satisfying diam(G_{2^k}) = k for all k ≥ 1."

* **(R1) per-k is literally false, and the source's own theorem already shows it at k = 2.**
  * CJKM Thm 4.22 (C2:2195–2219; = J Lemma 1.3(iv), J:115–116): every io G_n with n = 2^k + 2 has diameter 2.
  * At n = 4 = 2^1 + 2 there are two io graphs, A = 110 and A = 111. Both have diameter 2 = k.
  * A = 110 has edges {12, 13, 14, 23, 34} (5 edges); CG_4 has 4 edges. So it is ≇ CG_4.
  * Recomputed in `logs/s2_small.log`.
* **k = 3 also fails.** A = 1111110 is CG_8 plus the edge {1, 8}, with diameter 3 and 14 versus 13 edges
  (`logs/s2_small.log`, exhaustive over the 8 io sequences).
* **(R2) family reading is the intended statement.**
  * The "Moreover" clause of the companion Conjecture 1 (C2:2343–2348) — "PG_n is the only graph … whose diameter
    is 2 for all n ≥ 4" — is written in exactly the same "… for all n" form.
  * Read per n, that clause is false for every n = 2^k + 2 by the authors' own Thm 4.22 in the same paper. So the
    authors' "only … for all n" idiom must denote a family (one fixed g, all orders).
  * Conjecture 2 uses the same idiom. Reading it per-k would make it contradict the authors' own Thm 4.22 at
    n = 4.
  * Jung's Thms 3.2 and 3.3 (J:523–592) are stated only for k ≥ 4 and called "Conjecture 2 is true for some special
    … graphs" (J:146–147, 495–496). This is consistent with the authors knowing that small k behave differently.
  * I agree with the lane: (R2) is the reading that can carry credit. The per-k statement for k ≥ 4 is a
    strengthening.

### A.3 The io class must be the Thm 4.6 A-sequence class (new finding)

* CJKM Def. 4.1 says ⟨V_o⟩ "≅" G_{⌈n/2⌉}(g, f). Under the source's own reading this is a labelled equality: the
  proof of Thm 4.2 writes A(G(…)) = A(G(…)) as matrix equality (C2:1899–1903). Under that reading I checked all
  proper Bell-type prefixes for n = 4, 6, 8, 10, 12, 16: definition ⟺ Thm 4.6 form, with 0 exceptions
  (`logs/s1_construct.log`).
* Under an *unlabelled* finite reading of "≅", extra graphs qualify: 12 at n = 8 and 80 at n = 16, most with
  a_1 = 0 (`logs/s1b_unlabelled_extras.log`).
  * At n = 16 three of them have **diameter 5 > ⌊log₂ 16⌋**, contradicting CJKM Thm 4.22. Thirteen have diameter 4.
  * So that reading is not the source's notion, and it would break Thm 4.6 and Thm 4.22.
* The Lean definition must therefore be the Thm 4.6 / Lemma 2.1 A-sequence form, as the lane's draft does
  (`IoBell`, line 48), with this justification written down.

### A.4 Tables (claim check)

* **Table 1 (J:556–562; rendered page).** It has 9 rows for the 8 possible io sequences. 1111110 appears **twice**:
  diameter 2 (column 1, row 5) and diameter 3 (column 2, row 3). Every other sequence, including 1111001, appears
  exactly once.
  * The recomputed diameter of 1111110 is 3. The duplicate "1111110 → 2" row is the error.
  * **The lane's claim (proof.md:146–148) that the 9th row "should read 1111001, diameter 2" is wrong**: 1111001
    is already printed (column 2, row 1).
  * So the k = 3 exception *is* printed in Table 1 with diameter 3, but also with a contradictory diameter 2.
* **Table 2 (J:565–583)** has 31 rows but only 30 distinct sequences out of the 32 required.
  * 111111001111110 is duplicated.
  * **111111000000111 and 111111000011111 are missing.** I recomputed both: diameter 3.
  * Every printed diameter is correct (`logs/s2_small.log`).
  * Jung's computer-assisted Thm 3.3 therefore rests on an incomplete printed table, but its conclusion is true:
    my exhaustive k = 4 run is below.

### A.5 Endpoint(s)

* **E1 (primary):** (∀ k ≥ 1, diam CG_{2^k} = k) ∧ (∀ io A, (∀ k ≥ 1, diam G_{2^k}(A) = k) → A ≡ all ones).
  This is the intended (R2) statement with both clauses.
* **E0 (companion, zero credit):** the literal (R1) negation at k = 2 (and k = 3).
* **E3 (optional):** the per-k statement for k ≥ 4.

Under the 372205 precedent, "creditable only as a COMPLETE resolution of the intended problem" with the literal
negation included. E1 together with E0 is exactly that shape. The first clause (diam CG_{2^k} = k) is Jung's
published Thm 2.4, so it adds nothing to novelty but must be in the packet.

---

## B. Independent mathematics: PASS

### B.1 Lemma A (last-vertex neighbourhood): correct, but **not new**

* **Lagrange inversion.** n[z^n] f^j = j[w^{n−j}] A^n holds for f = zA(f) over any commutative ring. It is a
  universal polynomial identity, so lifting to ℤ is not even needed; one can work in GF(2) directly.
  * With n = N − 1 odd: [z^{N−1}] f^j ≡ j[w^{N−1−j}] A^{N−1}.
  * Frobenius gives A^N = A(w^N) ≡ 1 mod w^N, so A^{N−1} ≡ A^{−1} mod (2, w^N).
  * Correct. I checked the integer identity on 2,200 (n, j, A) triples with signed integer A, and Lemma A against
    the recurrence on 790 random Bell-type sequences (not only io), N = 4 … 128 (`logs/s4_lemmaA.log`).
* **The same formula is a corollary of the source's reverse-relabelling theorem.**
  * Sources: CJKM v2 Thm 3.14 (C2:1563; v1 Thm 3.9, C1:816) and Jung Lemma 2.3 (J:201–224):
    G^r_n = G_n((zA)′A^{n−2}, z/A).
  * Vertex N of G is vertex 1 of G^r, whose neighbours are read off the first column [z^{i−2}] (zA)′A^{N−2}.
  * Mod (2, z^N): A^{N−2} ≡ A^{−2}, and (zA)′/A² ≡ (z/A)′. So [z^{i−2}] (z/A)′ = (i−1)[z^{i−2}] A^{−1}, which with
    i = N + 1 − j is exactly Lemma A.
  * Jung used this very technique (reverse relabelling plus explicit coefficients) to compute a last-vertex
    neighbourhood in Thm 2.10 (J:433–461).
  * Machine check: the formula matches the literal label reversal on 320 graphs, and its first column equals Lemma
    A for every power-of-two N (`logs/s4_lemmaA.log`).
* The lane's "Lemma A (… ; new)" (proof.md:77) is therefore an overstatement. It is a re-derivation of a published
  lemma.

### B.2 Lemma B (first zero gives a low neighbour): correct; the genuinely new step

* p is even: if p were odd, a_{p−1} = a_p = 0 with p − 1 ≥ h, contradicting minimality (h is even).
* For io type, A ≡ (1 + w)H(w²).
* If H_m = 1 for m < q and H_q = 0, then (1 + x)H ≡ 1 + x^q + O(x^{q+1}).
* Then A^{−1} = (1 + w)U(w²) because (1 + w)² ≡ 1 + w². This gives [w^{2q}] A^{−1} = 1, j = N − 1 − 2q is odd,
  and 1 ≤ j ≤ h − 1.
* Correct. Checked exhaustively on the restricted families K = 3, 4, 5 (3, 15 and 255 sequences), on all 65,536
  sequences of the K = 6 restricted family, and on 60 random sequences at K = 7 (`logs/s5_lemmas.log`,
  `logs/s6_k6_p*.log`). No failures.
* Jung's Thm 3.2 is the case p = N − 2 (j = 1) only (J:523–552).

### B.3 Lemma C and the induction: correct

* V1 = [1, h+1] is G_{h+1} by (F), and has universal vertex h + 1 by (P1).
* V2 = [h+1, N] is G_h by (P2), which is CG_h because a_0 … a_{h−2} = 1.
* The four pair types are covered with bounds 2, K − 1, 1 + (K − 2) and 3. K ≥ 4 is used exactly once (3 ≤ K − 1)
  and is sharp at K = 3.
* This is Jung's Thm 3.2 argument (J:545–551) with the low neighbour j in place of vertex 1.
* Induction step: (P5) and (P4) force diam G_{2^k} = k. The induction hypothesis gives a_0 … a_{2^k−2} = 1, io gives
  a_{2^k−1} = 1, and then Lemma C applies. Correct.
* Simplifications:
  * (P3) is unnecessary: d_{CG_{2^s}}(1, v) ≤ diam CG_{2^s−1} ≤ s − 1 by (F) and (P4).
  * The V2 bound needs only diam CG_h ≤ K − 1, which is (P4), not Jung Thm 2.4.

### B.4 Published facts (located; hypotheses as used)

| Fact | Source location | Holds as used? |
|---|---|---|
| (P1) vertex 2^s+1 universal in G_{2^s+1} and G_{2^s+2} | CJKM Thm 4.13 (C2:2109–2125; C1:1562); Jung Lemma 1.3(i) (J:108–109) | Yes, for all io graphs and all s ≥ 0. My check covered 21,504 instances plus random N = 64 and 128. |
| (P2) ⟨{2^s+1, …, 2^{s+1}}⟩ ≅ G_{2^s} by shift | Jung Lemma 2.5(ii) (J:282–288), citing "[4, Theorem 3.7]", which matches neither arXiv version (C1 Thm 3.6 at C1:738; C2 Thm 3.11 at C2:1474 via Thm 3.9). The underlying identity A(f)^{2^s} = A(f^{2^s}) holds for every proper Bell type. | Yes, labelled. 10,752 checks plus random N = 64 and 128. |
| (P3) the distance-s pairs in CG_{2^s} | Jung Thm 2.6 (J:292–337); the full statement is in the proof's restatement (J:298–301) | Yes for s ≤ 8, but **not needed** (B.3). |
| (P4) diam G_n ≤ ⌊log₂ n⌋ | CJKM Thm 4.22 (C2:2195; C1:1650); Jung Lemma 1.3(iv) | Yes. 33,664 checks. |
| (P5) diam G_{2^{s+1}} ≤ max(2, diam G_{2^s} + 1) | Jung eq. (8) in the proof of Lemma 3.1 (J:499–504); Lemma 3.1 assumes k ≥ 2 | Yes, as used (s = k ≥ 4). 8,192 checks. |
| (F) leading principal submatrix | Definition (J:520–521) | Yes. 18,432 checks. |

The (P5) derivation in the lane (proof.md:73–74, "max(2, …)") is the correct form of Jung's (8).

### B.5 Finite claims, reproduced with my own code (`scripts/`, `logs/`)

| Claim | Lane | Reviewer |
|---|---|---|
| k = 1 | 1 graph, diameter 1 | same |
| k = 2 | (R1) fails, A = 110 | both io G_4 have diameter 2; 110 has 5 edges, CG_4 has 4 |
| k = 3 | (R1) fails, A = 1111110 | distribution {2: 6, 3: 2}; 1111110 = CG_8 + {1, 8} |
| k = 4 base (128) | {2: 61, 3: 66, 4: 1} | **{2: 61, 3: 66, 4: 1}**; the only diameter-4 graph is all-ones |
| k = 5 (32,768) | {2: 10881, 3: 21748, 4: 138, 5: 1} | **identical** |
| k = 6 restricted (65,536) | {4: 65532, 5: 3, 6: 1} | **identical**; Lemma B and Lemma C hold on all of them |

* The k = 4 base is already **Jung's Thm 3.3 at k = 4**: "first 16 entries not all 1s" covers every G_16 ≇ CG_16,
  since G_16 depends on a_0 … a_14 and a_15 = a_14. The proof there is computer-assisted with an incomplete
  Table 2 (A.4). So the base is published, and the lane's exhaustive run re-proves it.
* The lane does not say this (proof.md:118–122).

---

## C. Lean route: QUALIFIED_PASS (details in `LEAN-ROUTE.md`)

* **Cheapest literal endpoint:** E1 (R2 with both clauses) plus E0 (literal (R1) negation, `decide`).
* E1 needs **no induction over k, no P5, no general P1 or P2, and no Lagrange inversion**:
  * The first zero p at level K ≥ 4 gives diam G_{2^K} ≤ K − 1.
  * For p ∈ {2, 4, 6}, finite checks: 6 graphs of order 8 have diameter 2, and 16 graphs of order 16 have
    diameter 3. Both recomputed.
* Lemma A and B are replaced by two recurrence-only facts, both machine-checked (`logs/s7_route.log`):
  * a **dependence and perturbation lemma**: entries of gap p differ by (j+1)(a_p − a′_p) when A and A′ agree
    below p; checked on 254,589 entries;
  * a **mod-2 closed form for the Catalan Bell matrix**: b_{i,j} ≡ C(2i+1−j, i−j), proved by Pascal's rule. With
    Lucas this becomes the bit rule "x > y adjacent in CG iff (x−1) AND (x−1−y) = 0"; checked for rows 0–129.
* All Catalan facts follow from the bit rule by bit arithmetic: universal vertex, window shift, pendant last
  vertex, diam CG_n ≤ ⌊log₂ n⌋, and the lower bound diam CG_{2^k} ≥ k through an edge-length bound. The lower bound
  replaces Jung Thm 2.4's reversal proof.
* The k = 4 base need not be a 128-graph `decide`. Only upper bounds on 6 graphs of order 8 and 16 graphs of order
  16 are needed, and a one-directional soundness lemma for a bitmask ball checker suffices. No `native_decide`.
* **Cost:**
  * E1 + E0: about 1,600–3,100 lines, **MEDIUM**. The main risk is distance and walk transport in Mathlib.
  * E3 (per-k): add about 1,500–3,000 lines, **HIGH**, because general P1 needs division-free Lagrange–Bürmann or
    the CJKM edge-count lemmas, and general P2 needs the Frobenius power-series bridge.
* **Draft review** (`lean/Riordan337352.lean`): definitions are right (lines 24–30, 34–37, 48). Problems:
  1. the non-memoised `bell` is exponential, so `base_k4` cannot be `decide`d as written;
  2. `SimpleGraph.diam` needs a connectivity lemma;
  3. no isomorphism-form endpoint and no E0;
  4. the per-k route forces the heavy obligations;
  5. `diam_catalan` has no route;
  6. the io class definition (Thm 4.6 form) needs an explicit fidelity justification (A.3).

  Full list in `LEAN-ROUTE.md` §4. The lane's own estimate "HIGH, no finite-certificate shortcut" is right for its
  per-k route but too pessimistic for E1.

---

## D. Prior art: QUALIFIED_PASS (bounded)

OpenAlex, 2026-11-04 (all HTTP 200; `logs/openalex.log`, raw JSON in `oa/`):

* **Works citing Jung** (W2912691291, Graphs Combin. 38 (2022) 7, online 2021-12-15): 2.
  * CJKM I (LAA 2019);
  * Iamthong–Jung–Kitaev, "Encoding labelled p-Riordan graphs…", Graphs Combin. 2020 = arXiv:2009.01410. Its
    abstract (fetched, `dl2/`) concerns encodings by words and permutations, with no diameter result.
* **Works citing CJKM I** (W2962762546, LAA 579 (2019) 89–135, DOI 10.1016/j.laa.2019.05.033): 13 works:
  * Riordan graphs II;
  * word-representability of Toeplitz graphs and of split graphs;
  * integral cographs;
  * counting independent sets in Riordan graphs;
  * p-Riordan encodings;
  * Riordan posets;
  * Riordan–Krylov matrices;
  * a combinatorics group history;
  * Riordan-group commutators;
  * left multiplication operators;
  * Jung's diameter paper.

  None addresses Conjecture 2 beyond Jung's partial result.
* **Ji-Hwan Jung's works** (A5032277479, 26 works through 2024): no later Riordan-diameter paper. "Oriented Riordan
  graphs and their fractal property" (arXiv:2009.01677) is about oriented graphs (abstract fetched).
* **Searches:**
  * title "riordan graph(s)";
  * fulltext "Riordan graph" since 2021;
  * "Riordan graphs" diameter;
  * io-decomposable Riordan;
  * title "catalan graph".

  None found a "Riordan graphs III", a diameter or uniqueness result beyond Jung, or Lemma A's formula outside
  CJKM/Jung. 2026 Zenodo items (W7223699986 riordan-graph-enumerator; W7213927083 Catalan-graph independent sets)
  are unrelated.
* Lemma A's neighbour formula is *in the source family* through CJKM Thm 3.14 / Jung Lemma 2.3 (B.1).
* Limits:
  * no Google Scholar, MathSciNet or zbMATH;
  * no month-by-month scan of arXiv listing pages;
  * Crossref, Semantic Scholar, the arXiv search API and ScienceDirect were not used (denied routes);
  * no request was refused or retried.

---

## E. Significance and exclusion screen: QUALIFIED (borderline); root ruling required

For credit:

* It is a complete proof of the intended statement (R2), and also of the per-k statement for every k ≥ 4, for a
  conjecture posed in 2017 and restated as open in the 2019 journal version.
* A dedicated 2022 Graphs and Combinatorics paper by one of the four authors resolved it only for deviations within
  the first 16 entries, using computer tables (which are incomplete as printed). The authors had every ingredient
  and did not close it. This is evidence that the closing step was not obvious to them.
* This matches the 372205 line ("a full proof of the intended statement can qualify").
* It is not a parameter variant of the credited 338258 (Riordan graphs II, Conj. 7.7, spectral, a computed
  counterexample). It is a different paper, invariant and mechanism.

Against credit:

* Almost all of the proof is the authors' own machinery:
  * Lemma A = CJKM Thm 3.14 / Jung Lemma 2.3 read at vertex 1, the technique of Jung's Thm 2.10 (the lane calls it
    new; it is not);
  * Lemma C = Jung's Thm 3.2 proof with j for vertex 1;
  * the induction = Jung Lemma 3.1 plus CJKM Thm 4.22;
  * the base = Jung Thm 3.3 at k = 4.
* The **only new mathematics is Lemma B**, a four-line power-series observation. For io A ≡ (1+w)H(w²), the first
  zero at p = 2q gives [w^{2q}] A^{−1} = 1, so the last vertex gains a neighbour j = N−1−p in the low half.
* This is the profile of 347138 ("assembled from the authors' own ingredients … the new content is … a four-line
  case"), and of 371637 and 374241.
* Significance is modest: a niche structural conjecture, with 2 citing works for Jung and 13 for CJKM I.
* Family concentration: a second credit from the CJKM Riordan-graph series (I and II) beside 338258. This is not a
  variant, but root should weigh it.

**Reviewer's judgement.** Under the campaign's stated standard this is a genuine borderline case. The decisive
question is a policy one: does a short new lemma that closes an explicitly open published conjecture (intended
reading) outweigh the fact that every other step is the source's own machinery? 347138 was a refutation built from
the authors' own ingredients. This is a positive full resolution, which 372205 says can qualify.

I lean slightly toward eligibility, because the source author's own 2022 paper stopped short with the same tools.
I do not consider that lean strong enough to recommend Lean investment before root rules. If eligible, credit must
attach to E1 (with E0 packaged), and the paper must state plainly that:

* Lemma A is CJKM Thm 3.14 / Jung Lemma 2.3;
* Lemma C is Jung's Thm 3.2 argument;
* the base is Jung Thm 3.3;
* the new content is Lemma B (or, in the Lagrange-free route, the perturbation observation).

## Overall recommendation: **HOLD**

* The mathematics is correct and complete for E1 and for the per-k k ≥ 4 statement.
* Root should rule on gate E (372205 line versus 347138 line) before starting Lean.
* **If ruled eligible: PROCEED** to Lean with endpoint E1 plus E0 via the Lagrange-free route in `LEAN-ROUTE.md`
  (MEDIUM cost). Do not use the draft's per-k route unless E3 is explicitly wanted (HIGH cost).
* **If ruled a source-ingredient bridge: EXCLUDE** (zero credit). Keep the k = 2 observation and the Table 1/2
  errata as notes only.

## Required corrections to the lane's documents (if it proceeds)

1. proof.md:77 and SUMMARY: Lemma A is not new. It is CJKM v2 Thm 3.14 (v1 Thm 3.9) / Jung Lemma 2.3 read at
   vertex 1.
2. proof.md:146–148: the Table 1 "typo" correction is wrong. 1111110 is printed twice (diameters 2 and 3);
   1111001 is already present.
3. proof.md:118–122: the k = 4 base is Jung's Thm 3.3 at k = 4. Also note that Jung's Table 2 is incomplete (two
   sequences missing, one duplicated).
4. proof.md:30–32: add that (R1) fails at k = 2 already by CJKM's own Thm 4.22 (n = 4 = 2^1 + 2). The k = 2 failure
   is therefore printed in the source itself, not merely source-adjacent.
5. Add §A.3: the io class must be the Thm 4.6 A-sequence class. The unlabelled reading of Def. 4.1 admits graphs
   that violate Thm 4.22.
6. (P2) citation: Jung's "[4, Theorem 3.7]" matches neither arXiv version (C1 Thm 3.6; C2 Thms 3.9 and 3.11).
7. (P3) and Jung Thm 2.4 are not needed for the uniqueness part (B.3).

## Computations (all `python3 -I`, one at a time, under `scripts/run.sh`)

`scripts/run.sh` applies: taskset CPUs 0–1, `ulimit -t 120`, address space 3 GiB, `timeout 140`,
`MALLOC_ARENA_MAX=2`, TMPDIR in the lane.

| Script | Log and receipt | Purpose | CPU s | Max RSS |
|---|---|---|---|---|
| s1_construct.py | logs/s1_construct.* | recurrence vs power series; printed matrices; io definition vs Thm 4.6 | 3.2 | 13 MB |
| s1b_unlabelled_extras.py | logs/s1b_unlabelled_extras.* | unlabelled-reading sensitivity | 2.3 | 11 MB |
| s2_small.py | logs/s2_small.* | k = 1–4 exhaustive; (R1) failures; Tables 1 and 2 | 0.0 | 12 MB |
| s3_k5.py 0 1 | logs/s3_k5_full.* | k = 5 exhaustive | 3.9 | 11 MB |
| s4_lemmaA.py | logs/s4_lemmaA.* | Lagrange identity; Lemma A; reversal route | 0.2 | 12 MB |
| s5_lemmas.py | logs/s5_lemmas.* | (F), (P1)–(P5), Lemmas B and C (K ≤ 7) | 3.3 | 23 MB |
| s6_k6_restricted.py 0 2, 1 2 | logs/s6_k6_p0of2.*, p1of2.* | K = 6 restricted exhaustive | 15.2 + 15.1 | 12 MB |
| s7_route.py | logs/s7_route.* | facts for the Lagrange-free route; R2 finite cases | 0.3 | 12 MB |

* The `cpu_s` and `max_rss_kb` fields come from `/usr/bin/time -v` on the wrapper (it includes the waited-for
  child). Script and log sha256 values are in each receipt.
* Deviations, disclosed:
  * One 1/16 timing trial of s3 (2,048 sequences, 0.3 s) was run first and its log deleted before the full run.
    Its result is subsumed by `s3_k5_full`.
  * One OpenAlex query used a wrong guessed author id (A5056384013). Its output was deleted, and the deletion is
    noted in `logs/openalex.log`.
  * `python3 -I` ignores `PYTHONDONTWRITEBYTECODE`, so a `scripts/__pycache__` was created inside the lane. It was
    removed.
  * Nothing was written outside this lane. No background job is left.
