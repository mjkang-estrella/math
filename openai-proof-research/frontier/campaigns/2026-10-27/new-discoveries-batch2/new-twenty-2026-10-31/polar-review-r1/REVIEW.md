# REVIEW — MathDB 350432 (uniqueness conjecture for cograph minimal (∞,k)-polar obstructions)

Lane: polar-review-r1 (Claude, independent adversarial review before any Lean investment). Date 2026-11-05.
Reviewed object: `../expanded-corpus-r236/CANDIDATE.md` (sha256 `f41cfea0c1adb8828dbf609f5105d4ea539bdd72b7b915a6fca00b0d506af41f`,
the hash named in TASK.txt) and that lane's `lean-draft/PolarUniqueness.lean`. I did not import or execute any
discovery-lane script, and I did not run Lean, lake, leanchecker or a SAT/ILP solver. All code here is my own.

| Gate | Verdict |
|---|---|
| A Statement fidelity | **QUALIFIED_PASS** (exact on arXiv v1 and the 2023 thesis; the journal version could not be opened) |
| B Independent mathematics | **PASS** (I re-derived every step; no gap. My own exhaustive checks for k ≤ 5 agree) |
| C Prior art | **QUALIFIED_PASS** (bounded screen: no resolution found. OpenAlex stopped at a 429, as recorded) |
| D Significance / exclusion | **QUALIFIED_PASS** (not a one-paragraph bridge. But the lane overstates what is new, and the new part is short and elementary) |
| E Lean route | **QUALIFIED_PASS** (feasible with no cotree theory needed. Realistic cost is 3–5k lines. The draft is only a statement skeleton and probably does not compile as written) |
| **Overall** | **PROCEED** to Lean formalisation, under the conditions in §F |

---

## A. Statement fidelity

**Versions.** `https://arxiv.org/abs/2104.07852` returns 200. Its sha256 `7792a5ef…` is byte-identical to the discovery
copy. `…/abs/2104.07852v2` returns **404**, so v1 is the only arXiv version. A fresh download of
`https://arxiv.org/pdf/2104.07852v1` has sha256 `be9921a9…`, byte-identical to the discovery lane's PDF. So the line
numbers below, which refer to the discovery lane's text extraction
`expanded-corpus-r236/sources/text/2104.07852.txt` (hash-bound), describe the same document. The journal version
(OpenAlex: Discrete Math., doi 10.1016/j.disc.2021.112407, W3156627844) is behind ScienceDirect, which is denied, so
I did not read it. That is the qualification.

**Definitions in the source (quoted from v1).**
* (s,k)-polar (abstract, l.16–20): "An (s, k)-polar partition of a graph G is a partition (A, B) of its vertex set
  such that A induces a complete multipartite graph with at most s parts, and B induces the disjoint union of at most
  k cliques with no other edges. A graph G is said to be (s, k)-polar if it admits an (s, k)-polar partition. The
  concepts of (s, ∞)-, (∞, k)-, and (∞, ∞)-polar graphs can be analogously defined." In the body (l.71–80): "A cluster
  is the complement of a complete multipartite graph, and … a k-cluster is a cluster with at most k components …
  We will use ∞ instead of s, k or both, to indicate that the number of parts … is unbounded."
* Cograph (l.15, 56–57): P4-free graph. The cotree is introduced at l.58–65.
* Minimal obstruction (l.84–86): "A cograph (s, k)-polar obstruction is a cograph which is not (s, k)-polar, and a
  cograph minimal (s, k)-polar obstruction is a cograph (s, k)-polar obstruction such that every proper induced
  subgraph is (s, k)-polar."
* Type (l.128–130): "Let k, c, i be integers such that 0 ≤ i < c ≤ k + 2. We say that a cograph minimal (∞, k)-polar
  obstruction has type (c, i) if it has exactly c connected components and precisely i of them are trivial." (A
  trivial component is a K1, l.125.)
* Structure results: Lemma 5 (l.187–199; at most k+2 components, ≥1 non-trivial component, ≤k+1 trivial components,
  at most one non-complete component if there is an isolated vertex, complete components of order ≤ 2; "proof …
  omitted", l.184–185). Remark 4 (l.181–182; K1+(k+1)K2 is the only cluster obstruction). Lemma 17 (l.583–595, proof
  omitted). **Theorem 25** (l.803–809, recursion): type (k−j+2, p) with 1 ≤ p ≤ k−j holds iff G ≅ K2 + G′, where G′ is a
  minimal (∞,k−1)-polar obstruction of type (k−j+1, p) that is (1,k)-polar.
* Uniqueness already proved: **Corollary 26** (l.835–847) gives uniqueness for types (k+2,p), p ≤ k; (k+1,p), p ≤ k−1;
  (k,p), p ≤ k−2, with the normal forms pK1+(k−p+1)K2+K_{p,p}, pK1+(k−p)K2+(K̄2⊕(K2+pK1)) and
  pK1+(k−p−1)K2+(K1⊕(2K2+pK1)). Text extraction loses the complement bars; I checked the bars against my own census
  in §B. Theorems 27/28 (l.867–946) list all obstructions for k = 2 (23) and k = 3 (49). Section 7 (l.956–961) says the
  types (c,c−1), c ∈ {3,…,k−1}, have no recursive characterisation and that "our techniques might not be enough".
* **Conjecture 1** (l.972–973): "Let k, c and i be integers such that 1 ≤ i ≤ c − 2 ≤ k. Then, there exists exactly
  one cograph minimal (∞, k)-polar obstruction of type (c, i)."

**Comparison with the MathDB literal** (`expanded-corpus-r236/raw/350432.jsonl`, l.1). The definitions, the range
1 ≤ i ≤ c−2 ≤ k and "there exists exactly one" are reproduced faithfully. The record's trailing sentence ("This extends
the cases …") is commentary. *Existence is part of the claim* ("there exists exactly one"). "Exactly one" means up to
isomorphism. The source never says so in the conjecture itself, but it is the only sensible reading, and l.830–831
plus Corollary 26 ("up to isomorphism, this is the only …") use it so. The type definition's side condition
c ≤ k+2 holds automatically in the range. CANDIDATE.md l.8–23 restates all of this correctly.

**Later restatements.** In Contreras-Mendoza's April 2023 UNAM thesis (`sources/cm-thesis-0837616.pdf`, read only, not
copied), Conjecture 3.27 at extraction l.2031–2032 has the same wording and is listed under "Open problems and
conjectures" (§3.4). The 2024 Graphs Combin. follow-up (arXiv:2203.04953 = doi 10.1007/s00373-024-02784-7) mentions
(∞,k)-polar obstructions only as prior work (extraction l.125, reference l.1226). The DMTCS 2024 paper
(arXiv:2210.02497 = doi 10.46298/dmtcs.11479; fresh download sha256 `40628841…`, my own pdftotext) treats 2-polarity
only. It has no occurrence of "conjecture" or "(∞, k)". No statement change anywhere.

## B. Independent mathematics

### B.1 Line-by-line check of CANDIDATE.md §3 (l.42–146)

I re-derived every step on paper. Results:

* **Heredity, one-vertex minimality, cograph minimality = graph minimality** (l.47–49): correct.
* **F1** (l.52–54) is correct: if uv is an edge, every vertex is adjacent to u or to v. **F2** (l.55) and **F3**
  (l.56–57) are correct; in F3, a cluster meeting both sides of a join is connected, hence a single clique.
  **F4** is Seinsche. It is the only cograph-specific fact used in the whole proof, once, in Lemma 5.
* **Lemma 1** (l.62–67) is correct. A CM subset of a cluster is edgeless or a clique (F2). The two minima are r′ and c−1.
* **Lemma 2** (l.69–73) is correct and is exactly source Lemma 5(4). A CM side with an edge is connected, so every
  other component sits in the cluster side as a whole clique.
* **Case I** (l.75–79) is correct. Small presentational gap: "deleting an isolated vertex" needs i ≥ 1. That holds in
  range, but the text should say so. The conclusion is source Remark 4.
* **Lemma 3** (l.84–91) is correct in both directions. The ⇒ direction uses that Q is non-complete, to exclude A
  sitting inside a K1 or K_{s_j} component.
* **Lemma 4** (l.93–94) is correct and is source Lemma 5(5).
* **Range bookkeeping** (l.96–97): r = c−i−1 ≥ 1 and ℓ = k−r ≥ i−1 ≥ 0. Correct.
* **(C1)–(C5)** (l.98–101) are correct and, together, equivalent to minimality. (C4) is obtained by Lemma 3 on
  (i+1)K1+(r−1)K2+Q plus (C2). This is the same mechanism as the source's Theorem 25 proof (l.821–823; see §D).
* **Lemma 5** (l.103–106) is correct. (A,B) is a (1,ℓ+1)-partition and Q is not (1,ℓ)-polar, so B has exactly ℓ+1 ≥ 2
  cliques and is disconnected. Q = X⊕Y (F4). By F3, B lies on one side, say Y. Then X ⊆ A, and since A is edgeless and
  meets X, A ⊆ X. So A = X and B = Y.
* **Lemma 6** (l.108–122) is correct, including the converse constructions. (a) An edgeless A lies on one side. If
  A ⊊ I, then B is a clique containing C, impossible because m ≥ 2. If A ⊆ C with A ≠ C, then B = I ∪ (C∖A) is a single
  clique, which forces a = 1 and β ≤ 1. (b) The three cases (B meets both sides, B ⊆ I, B ⊆ C) are exhaustive, and B = ∅
  is covered by B ⊆ I.
* **ℓ = 0** (l.124–128) is correct. Here i = 1 and r = k. Q is CM and split, so Q = K_t ⊕ K̄_a with a ≥ 2. For a ≥ 3 the
  deletion stays non-polar by Lemma 3. For a = 2, G−v is a cluster with k+2 components, k+1 of them non-trivial. So no
  Case II obstruction exists with ℓ = 0.
* **ℓ ≥ 1** (l.130–142). I re-derived the (C1)–(C3) translations and (v1)–(v5) from Lemma 6 (with p = ℓ = m−1) and
  Lemma 1. In (v1), (v3) and (v4), Q−v is still connected (a ≥ 1 remains) and non-complete (m ≥ 2 remains), so Lemma 3
  applies. The text leaves this implicit.
  * β = 0 gives a ≥ ℓ+1 (C1), i ≥ ℓ+1 (C2), i ≤ ℓ+1 (range) and a ≤ ℓ+1 (v1). So Q = K_{i,i}, i ≥ 2, c = k+2.
  * β = 1 gives a = 2 (C1, v1) and i = ℓ (C2, C3; the i = 1 sub-case forces ℓ = 1). (v4) holds through its third
    disjunct. So Q = K̄2 ⊕ (K2 + iK1), c = k+1.
  * β ≥ 2 gives a = 1 (v1 fails otherwise) and β = ℓ−i+1 (C2, C3, v2; for i = 1 use C2 and v2). (v4) holds with
    equality. So Q = K1 ⊕ (βK2 + iK1) with β = k−c+2, i.e. c ≤ k.
  The three branches give disjoint values of c, so each in-range type has at most one Case II obstruction. Case I
  gives only (k+2,1), and Case II with ℓ ≥ 1 and c = k+2 needs i ≥ 2. The converse checks (existence) are equivalences,
  as claimed at l.144. **No gap found.**
* The normal forms (l.33–37) agree with Corollary 26 for c ∈ {k, k+1, k+2}. With bars restored, K2 ⊕ (K2+pK1) reads
  2K1 ⊕ (K2+pK1), as in source Theorem 27(4).

Minor issues in CANDIDATE.md (none affects correctness):
1. l.155–156 call "in the conjectured range there is a K2 component; deleting one of its vertices forces
   (1,ℓ+1)-polarity" the "decisive new step". It is not new. The source states that these types have a K2 component
   (l.130–133, l.818) and proves exactly this deletion argument in Theorem 25 (l.821–823). See §D.
2. l.165 attributes 43,930 cographs at n = 12 to OEIS A000669. My enumeration confirms 43,930 *cographs* (and 21,965
   connected ones). From memory, not checked online: A000669 is the connected / series-reduced count and A000084 the
   all-cograph count. This is a citation slip only.
3. Case I (l.75–79) should say that an isolated vertex exists because i ≥ 1.

### B.2 Reviewer's own computations (`scripts/polar_review.py`, written from scratch)

**Method.** Unlabelled cographs are enumerated as canonical cotrees (sorted, alternating, nested tuples), so
isomorphism means tuple equality. Exact polarity uses a cotree DP with states (a,b): a ∈ {A empty, A edgeless
nonempty, A CM with an edge}, b ∈ {B empty, B one clique, B ≥ 2 cliques}, each mapped to the least clique count of B.
*Union:* the A-sides X+Y are CM iff one side is empty or both are edgeless; clique counts add. *Join:* the A-sides are
always CM; the B-sides X⊕Y form a cluster iff one side is empty or both are single cliques, giving one clique. These
rules are F1/F3. A graph is a minimal (∞,k)-obstruction iff max_v minval(G−v) ≤ k < minval(G).

**Self-test** (`logs/selftest-brute10.log`):
* cograph counts for n = 1..12 are 1, 2, 4, 10, 24, 66, 180, 522, 1532, 4624, 14136, 43930 (standard);
* for n ≤ 5, the iso classes of all labelled P4-free graphs equal the generated set;
* the DP equals brute force over all 2^n partitions, for both (∞,·) and (1,·), on **every cograph with n ≤ 10**
  (6,965 graphs);
* the leaf-deletion routine equals explicit vertex deletion for n ≤ 6;
* 0 failures.

Earlier logs `selftest-brute8.log` and `selftest-brute8-run2.log` are partial runs that stopped on a bug in my code:
empty `min()` for non-polar graphs. They are kept unmodified.

**(B-i) Full census, unstructured** (`outputs-census-N14-K5.json`). I enumerated **every unlabelled cograph of order
≤ 14** (1+2+4+10+24+66+180+522+1532+4624+14136+43930+137908+437502 = **640,441** graphs) and found
every minimal (∞,k)-polar obstruction for k = 0..5.
* k = 2: **23** obstructions. k = 3: **49**. Both match source Theorems 27/28.
* The per-type counts match the source lists. For k = 2: (1,0):4, (2,0)+(3,0):3, (2,1):4, (3,1):1, (3,2):7, (4,1):1,
  (4,2):1, (4,3):2. For k = 3: (5,4):2, (4,3):7, (3,2):8, (2,1):9, and 1 each for (3,1), (4,1), (4,2), (5,1), (5,2),
  (5,3).
* For k ≤ 5, every in-range type whose normal form has order ≤ 14 has **exactly one** obstruction, equal to P(k,c,i).
  In-range types whose normal form is larger have none of order ≤ 14.
* This covers the open types for k = 4 (type (3,1), order 11) and k = 5 (types (3,1), (4,1), (4,2), order 13).
* An earlier run through order 12 (`outputs-census-N12-K5.json`) agrees.

**(B-ii) Structured exhaustive, every admissible (k,c,i) with k ≤ 5** (all 35 types;
`outputs-structured-Q14-K5.json`). The family is all graphs G = iK1 + ΣK_{s_j} + Q, where:
* Q ranges over **every connected non-complete cograph of order 3..14** (320,207 graphs);
* s_j ∈ {2,3}, which also tests Lemma 4;
* clusters iK1 + ΣK_{s_j} with s_j ∈ {2,3,4} are included as well.

By Lemma 2 (= source Lemma 5(4), which I re-proved), this family contains every obstruction of type (c,i), i ≥ 1, whose
non-complete component has order ≤ 14. The normal forms have |Q| ≤ 10 for k ≤ 5, so the margin is ≥ 4. Result: every
one of the 35 types has exactly the one obstruction P(k,c,i) (`ALL_OK True`). This reaches the largest normal forms
(order 3k+2 = 17 at k = 5).

**Limits.** These enumerations are finite (order ≤ 14, or |Q| ≤ 14). They corroborate the proof; they do not replace it.

**(B-iii) Lemma checks** (`outputs-lemmas-Q13-run2.json`). Zero violations in each:
* Lemma 5: every connected cograph of order ≤ 13 that is (1,ℓ+1)-polar but not (1,ℓ)-polar, ℓ ≥ 1, has shape
  K̄_a ⊕ (cluster with ℓ+1 cliques). 708 instances.
* Lemma 6: formulas (a) and (b) for a ≤ 6, m ≤ 6, clique sizes ≤ 4. 14,508 instances.
* Lemma 1: 2,961 instances.
* Lemma 3: 669,312 instances.

The first lemma run (`outputs-lemmas-Q13.json`) reported "violations". That was a bug in my harness: it tested graphs
that are not (1,∞)-polar at all, such as K1⊕C4. It is documented in `logs/stdout-transcripts.md` and kept.

## C. Prior art (bounded; receipts in `downloads/d1…d6/*.receipt.json`)

* **OpenAlex.** The source record is W3156627844. `filter=cites:W3156627844` returns **one** citing work: the authors'
  own Graphs Combin. 2024 paper, which does not resolve the conjecture (§A). Contreras-Mendoza's works (A5049025080,
  10 records, newest 2026-06) are:
  * DMTCS 2024 (2-polarity only, checked in full text);
  * Graphs Combin. 2024;
  * "Polarity on H-split graphs" (DAM 2026, doi 10.1016/j.dam.2025.12.065, and the Procedia 2023 version). From its
    title this concerns a different class. **Body not inspected:** OpenAlex returned **429** on my fifth query, and I
    did not retry it or use OpenAlex again;
  * star colouring (arXiv:2606.25168);
  * a P5-free partition paper;
  * (2,1)-colouring algorithms;
  * the 2018/2020 (s,1) and planar papers.
  None mentions (∞,k)-obstruction types in its title. A title search ("minimal obstructions polarity cographs",
  11 hits) includes Ekim–Hell–Stacho–de Werra, *Polarity of chordal graphs* (DAM 2008), and
  Hell–Hernández-Cruz–Linhares-Sales (2-polar cographs). Neither touches this conjecture, and both predate it.
* **2023 thesis:** Conjecture 3.27 is still open (§A).
* **GitHub:** 4 unauthenticated, spaced repository searches (≤ 8 allowed). "polar cograph": 0. "cograph obstructions": 0.
  "polarity graphs obstruction": 0. "cograph lean": 1, `jtraverso/chordal-split-threshold-graphs`, which is the
  structural library already in Lean Pool and has no polarity content.
* **Lean Pool** at HEAD `01db1d7049cf9668bda1e9e106875ee1278b43e6` (committed 2026-10-07):
  * `LeanPool/projects.yml` (663,100 bytes) has one cograph project, `structural-graph-classes`: cotree
    representation, Seinsche union/join roots, twins. It has no polarity.
  * `candidates/` (README, discovered.yml, shortlist, decisions.jsonl, manual.txt) has no hit for cograph, polar,
    2104.07852, 350432 or either author.
  * Note: the discovery lane's `sources/leanpool-projects.yml` is a 14-byte file, apparently a 404 body from a wrong
    path. Its registry claim was therefore weaker than stated; this review supplies the real file.
* **Not covered:** Crossref, Semantic Scholar, the arXiv search API, ScienceDirect and DBLP (all denied); Google Scholar;
  MathDB live (not fetched; the record retrieved 2026-09-29 shows `solutions: []`).
* **Verdict:** no public resolution found within these bounds.

## D. Significance and exclusion screen (crucial)

**Which steps are source or classical, and which are new:**

| Step in CANDIDATE.md | Status |
|---|---|
| F1–F3 (l.52–57) | classical folklore |
| F4 Seinsche (l.58–60) | classical; already in Lean Pool |
| Lemma 1 (l.62–67) | ⇐ direction is the source's observation l.175–178; Case I = source Remark 4 |
| Lemma 2 (l.69–73), Lemma 4 (l.93–94) | source Lemma 5(4),(5), reproved (the source omits the proof) |
| Lemma 3 (l.84–91) | routine generalisation of the source's Lemma 12/17 conditions (r = 0) |
| (C4): a K2 component exists, and deleting one of its vertices forces (1,ℓ+1)-polarity | **source Theorem 25 proof, l.818–823** (and l.130–133) |
| ℓ = 0; branches β = 0, 1, 2 (c = k+2, k+1, k) | re-derive source Corollary 26 (items 1–3) |
| **Lemma 5** (l.103–106): a connected cograph that is (1,ℓ+1)- but not (1,ℓ)-polar is K̄_a ⊕ cluster | **new** (5 lines) |
| **Lemma 6** (l.108–122): exact polarity of K̄_a ⊕ C | **new** (routine calculation, ~15 lines) |
| **Branch β ≥ 3** (c ≤ k−1, the open part) | **new** (3 lines, given Lemmas 5–6) |

**Equivalent source-based route.** Iterating source Theorem 25 r = c−i−1 times reduces Conjecture 1 to the following
claim. For ℓ ≥ i−1, exactly one minimal (∞,ℓ)-obstruction of type (i+1,i) is (1,ℓ+1)-polar. (K2+G′ is (1,m+1)-polar
iff G′ is (1,m)-polar, so the intermediate conditions collapse.) The authors needed the full lists of type (c,c−1) for
this step. They had those lists only for c ∈ {k′+1, k′+2} (Theorem 19, Corollaries 23–24), and they call the general
(c,c−1) case "a very difficult task" (l.642–645) and possibly out of reach of their techniques (l.959–961). The
candidate's actual contribution is to see that the list is not needed. Inside the (1,ℓ+1)-polar subclass, Lemma 5
pins down the structure rigidly, and Lemma 6 then finishes the classification.

**Weighing the precedents.**
* *Against exclusion:*
  * 374241 was a one-paragraph bridge from a printed corollary. 371637 was a routine corollary of one printed lemma.
    Here no printed result yields the conjecture: the conjecture is "source Theorem 25 + Lemma 17 + a new structural
    lemma and classification", about one page of new argument.
  * The authors held Theorem 25 when they posed the conjecture, and they repeated it as open two years later
    (thesis, 2023).
  * The resolution is complete, full-scope and constructive. It gives explicit normal forms and existence, not a
    parameter instance.
  * Shortness alone is not routine adaptation (batch2 AGENTS.md).
* *For exclusion:*
  * The reduction step and most of the case analysis are the source's own mechanisms.
  * The new ingredient is elementary: one application of Seinsche plus bookkeeping. An expert who set out to
    classify the (1,k+1)-polar base obstructions could plausibly find it quickly.
  * The topic is niche.
  * The candidate's own novelty narrative (l.154–160) misattributes the K2-deletion step to itself.

**Reviewer's decision.** This is **not** a short source-ingredient bridge in the sense of 374241 or 371637. The
decisive rigidity lemma (Lemma 5) and the open-range classification (β ≥ 3) are absent from the source and its
sequels, and no printed result gives the conjecture in a paragraph. It is, however, a *modest* result: an
elementary, about one-page new argument on top of the source's own recursion. Gate D: **QUALIFIED_PASS.**
Recommendation: **PROCEED**, conditional on §F. If root applies the stricter reading, that any ≤ 1-page elementary
completion on top of the source's own reduction theorem is a bridge, the correct outcome is EXCLUDE. Root should
record that choice explicitly before spending Lean effort.

## E. Lean route

**Cheapest literal endpoint.** Plain `SimpleGraph V`, `[Fintype V] [DecidableEq V]`, with:
* cograph := induced-P4-free;
* (s,k)-polar := ∃ A : Finset V, with A complete multipartite (non-adjacency transitive on A) and Aᶜ a cluster
  (adjacency transitive) whose induced subgraph has `Nat.card ConnectedComponent ≤ k`;
* minimal obstruction := P4-free ∧ ¬polar ∧ every `G.induce S`, S ≠ univ, polar;
* type := `Nat.card G.ConnectedComponent = c` ∧ #{v | ∀ w, ¬G.Adj v w} = i.

Endpoint, ∀ k c i with 1 ≤ i, i+2 ≤ c, c ≤ k+2:
* existence: ∃ n, ∃ G : SimpleGraph (Fin n), MinObs k G ∧ type G c i;
* uniqueness: ∀ V W (Fintype) G H, MinObs k G → type G c i → MinObs k H → type H c i → Nonempty (G ≃g H).

Quantify uniqueness over arbitrary Fintype types, not just `Fin n`. That is literal and costs nothing extra.

**No cotree theory is needed.** The only cograph fact the proof uses is Seinsche's decomposition, applied once to Q in
Lemma 5. Lean Pool supplies it:
* `SimpleGraph.IsP4Free.not_preconnected_or_compl` (`LeanPool/StructuralGraphClasses/CographDecomposition.lean`
  l.153, 7,125 bytes; plus `IsCograph.exists_join_root`);
* but Lean Pool is pinned to Lean **v4.35.0-rc3** and mathlib **c55e6e78**, while the draft targets Lean 4.34.1 and
  mathlib d13f23b7. It cannot be imported directly, so port it with attribution (≈ 150–300 lines).

**Cost drivers:**
1. Component bookkeeping for disjoint unions (component counts, isolated vertices, complete components, and the
   "A with an edge lies in one component" argument).
2. The polarity calculus (Lemmas 1, 3, 6) on induced subsets.
3. An explicit isomorphism to a normal form. Build the model on a sum type, Fin i ⊕ (Fin r × Fin 2) ⊕ X, so that
   `Equiv.sumCongr` does the work, and transport it to `Fin n` only for existence.
4. Existence: show the three models are minimal obstructions of the right type.

Realistic estimate: **3–5k lines**, several formalisation sessions. There are no exotic dependencies.

**Draft assessment** (`lean-draft/PolarUniqueness.lean`, 68 lines): a statement skeleton with a single `sorry`. It
contains no proof content. The definitions are faithful:
* `IsCMSet` (l.23–24), `IsClusterSet` (l.30–31), `numCliques` (l.34–35), `IsInfPolar` (l.38–39) and `IsMinObs`
  (l.46–48) match the source;
* `IsP4Free` (l.17–19) correctly encodes "every path a-b-c-d with ac, bd non-edges closes to a C4".

Expected compile problems and fidelity notes:
* `HasType` (l.51–52) uses `G.degree` and `univ.filter`, which need `DecidableRel G.Adj` and a decidable predicate. These
  are missing from the `variable` line (l.14), so it should fail to elaborate without `open Classical` or an extra
  instance. Fix: define isolated vertices as `∀ w, ¬ G.Adj v w`, with classical decidability.
* The uniqueness clause (l.57–58) is restricted to `Fin n`/`Fin m`. Generalise it as above.
* The local `IsP4Free` will need a proved bridge to Lean Pool's `SimpleGraph.IsP4Free` if Seinsche is ported.
* Instance resolution for `IsInfPolar` on `↥(S : Set V)` in `IsMinObs` should be checked when compiled.

None of these is a fidelity defect in the statement itself.

## F. Overall recommendation: **PROCEED** (to Lean formalisation), with conditions

1. Root records the Gate D significance judgement explicitly against 374241/371637, using the table in §D, before any
   Lean investment. Under the stricter reading the outcome would be EXCLUDE.
2. Rewrite the novelty statement in CANDIDATE.md l.154–160. Credit source Theorem 25 (l.803–829) for the K2-deletion
   and (1,k)-polarity mechanism and for the reduction. Present the new content as Lemma 5, Lemma 6 and the c ≤ k−1
   classification. Fix the OEIS citation, and state i ≥ 1 in Case I.
3. Use the Lean endpoint of §E: uniqueness over arbitrary Fintype types, existence on Fin n, a ported Seinsche lemma,
   and no cotree equivalence. The draft's decidability issues must be fixed. An independent statement-fidelity review
   of the compiled endpoint is still required.
4. Before acceptance, close the residual prior-art gaps: re-query OpenAlex after its quota resets, and check the
   bodies of "Polarity on H-split graphs" (DAM 2026 / Procedia 2023).

## Files

* Scripts: `scripts/polar_review.py`, `scripts/fetch.py`, `scripts/oa.py`, `scripts/inspect.py`, `scripts/textify.py`.
* Fetch plans: `plans/plan1…plan6`.
* Downloads and receipts: `downloads/d1…d6` (fresh, empty-at-creation directories).
* Outputs:
  * `outputs-census-N12-K5.json`, `outputs-census-N14-K5.json`
  * `outputs-structured-Q12-K5.json`, `outputs-structured-Q14-K5.json`
  * `outputs-lemmas-Q13.json` (first run, harness bug), `outputs-lemmas-Q13-run2.json`
  * `text-2210.02497.txt`
* Logs: `logs/selftest-*.log`, `logs/stdout-transcripts.md`.
* Input hashes: `hashes-before.json` and `hashes-after.json`. Both cover 202 files: the whole discovery lane, TASK.txt
  and the three AGENTS.md files. They are **identical**, and the digest of each JSON is `b904ad9e…619a`.
