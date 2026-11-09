# ACTUALBRIEF — expanded-corpus-r535

Lane: `expanded-corpus-r535`
Campaign: `new-twenty-2026-10-31`
Fixed twenty IDs (no reselection): 364214, 382400, 363863, 366291, 360766, 360918, 359765, 351797, 344498, 339456, 341444, 334183, 334728, 319113, 319212, 367700, 364265, 356524, 317625, 376715.

Counts: 20 gates; 3 deep routes; 2 dead targets (source-owned); 15 parked; **0 qualified survivors**.
Outputs authored: `results.json` (20 ID-keyed gates), this brief. **No `FULLCANDIDATE.md` and no `DORMANT-SOL-FORMAL-PLAN.md`** — nothing in this lane reached the acceptance bar.

---

## 1. Literal binding (all 20)

Every gate is bound to the exact corpus line, including its trailing newline, at the line level (`raw_line_sha256`), at the raw JSON statement token level, and at the decoded-UTF-8 level. Full per-ID fields are in `results.json`; this table is the summary.

| # | ID | chunk | line | raw len | raw sha256 (head) | decoded len | title |
|---|----|-------|------|---------|-------------------|-------------|-------|
| 1 | 364214 | 0010 | 3435 | 1597 | 9086b123 | 395 | O'Neill Möbius bound, regular Tesler matrices |
| 2 | 382400 | 0014 | 1426 | 2010 | 73d0cb40 | 633 | unique-obstruction Hamilton decompositions, tripartite tournaments |
| 3 | 363863 | 0010 | 3087 | 1832 | 2439092d | 608 | discrete Babenko–Beckner, interval-supported |
| 4 | 366291 | 0011 | 494 | 1780 | 39e4e196 | 552 | Payne–Wood colouring conjecture |
| 5 | 360766 | 0010 | 14 | 1994 | 2ec44e8d | 622 | transience of WUSF ∪ ε-WUSF on transitive transient graphs |
| 6 | 360918 | 0010 | 164 | 1754 | 38d9148f | 513 | common-card bound, bipartite vs non-bipartite |
| 7 | 359765 | 0009 | 4021 | 2109 | f8058c8f | 647 | Hasheminezhad–McKay regular partitions of K_n |
| 8 | 351797 | 0008 | 1124 | 1821 | 1fc85b3d | 572 | neighbourhood-island conjecture |
| 9 | 344498 | 0006 | 3876 | 1659 | a23cc044 | 463 | subsquare extension for Cayley tables |
| 10 | 339456 | 0005 | 3863 | 1827 | 63b2d73d | 587 | rectilinear crossing number, K^d_{2d} |
| 11 | 341444 | 0006 | 841 | 1830 | 07012fbb | 655 | entropy conjecture for tournament digraphs |
| 12 | 334183 | 0004 | 3627 | 2022 | 7e7d06c5 | 769 | De Joannis de Verclos–Kang–Pastor, squares of claw-free graphs |
| 13 | 334728 | 0004 | 4167 | 1966 | adaae4bd | 718 | uniqueness of tournament-kernel representatives |
| 14 | 319113 | 0001 | 3687 | 1838 | 7d7abf2d | 651 | planar minimal graphs with arbitrarily many vertices |
| 15 | 319212 | 0001 | 3786 | 1607 | ef56cf39 | 425 | Leonardness of completely regular codes |
| 16 | 367700 | 0011 | 1888 | 2029 | 0ea2174f | 803 | Θ(N² log N) pebble motion on trees |
| 17 | 364265 | 0010 | 3485 | 2116 | 923df1e4 | 891 | McKinley–Spiro random Turán, bipartite F |
| 18 | 356524 | 0009 | 814 | 2432 | 56a1660d | 1177 | two-sided local limit, diffusion approximation |
| 19 | 317625 | 0001 | 2211 | 2074 | 60a9f5a3 | 850 | large girth for cubic graphs of maximal complexity |
| 20 | 376715 | 0013 | 782 | 2634 | fb75bea8 | 1348 | split localization entropy universality |

Chunk hashes: 0001 `e9630322…`, 0004 `c607c6f6…`, 0005 `026158d6…`, 0006 `1dd3c173…`, 0008 `b99fabbe…`, 0009 `e2f7f18e…`, 0010 `404b7005…`, 0011 `97bd035b…`, 0013 `a09279df…`, 0014 `5d123177…` (full values in `results.json`).

---

## 2. Deep route 364214 — O'Neill's |μ(0̂,A)| ≤ n! for the regular Tesler poset

**Statement.** For α = (1,…,1) and A ∈ T(1ⁿ), the Möbius value satisfies |μ(0̂,A)| ≤ n!. O'Neill, *On the poset and asymptotics of Tesler matrices*, EJC 25(2) Paper 2.4 (2018), Conjecture 6.7; restated as open in arXiv:2408.01513.

**Sources read.** arXiv:2408.01513 (Definitions 2.3–2.5 hook sums, Conjecture 2.1, Definition 3.1 merge covers) and arXiv:1702.00866 in full (Prop. 3.3 rank = # off-diagonal entries; Prop. 3.5/Cor. 3.6 Boolean base; Lemma 2.4 Hallam–Sagan χ(Q/~;q)=χ(Q;q); Lemmas 4.4/4.6/4.8; Prop. 4.7; Theorem 4.9 Armstrong χ(P(1ⁿ);q)=(q−1)^C(n,2); Prop. 6.6; Conjecture 6.7 with verification to n=5).

**My analysis.** The recursive construction exhibits P(1ⁿ) as a quotient of P(1,0,…,0) × B_{n−1} × ⋯ × B_1: a class at the step that fixes hook sum position n−r+1 is {(A,S) : A+S = X} with S a subset of the r−1 already-free coordinates, so class size ≤ 2^{r−1}. Multiplying gives the *trivial* bound ∏ 2^{r−1} = 2^C(n,2), which is exactly what O'Neill states as the easy upper bound (eq. 12: n! ≤ T(1ⁿ) ≤ 2^C(n,2)). The conjecture's content is therefore a **per-step cancellation**: the signed sum over each class must shrink by roughly a factor of n at each of the n−1 steps, since n! = ∏_{r=1}^{n−1}(r+1) against ∏ 2^{r−1}.

I could not extract that cancellation. The quotient is a lattice congruence, so χ is preserved, but χ alone gives only the *aggregate* identity Σ_A μ(0̂,A) = (−1)^{C(n,2)} — no per-element control. Armstrong's (q−1)^C(n,2) says the rank generating function of μ is a pure power, i.e. the μ-mass is spread over all ranks in a very specific way, but it constrains the *sum over each rank*, not individual elements. The printed n=3 values (μ ∈ {−1,−1,−1,2,1,−1}, max 2 ≤ 6) are consistent but give no extrapolation.

**Gap, stated precisely.** What is missing is a bound on |μ(0̂,A)| for a single A, not on rank-sums. A proof needs either (a) an explicit injection from the "cancellation support" of each A into permutations of [n], or (b) a recursion in n with multiplicative factor ≤ n at each step. Neither is available in the source or in my analysis. The 2^{r−1} class sizes are not obviously reducible: the class is an antichain in the Boolean factor, and its members' μ-contributions are not known to cancel pairwise.

**Lean endpoint.** For `n : Nat`, `A : Matrix (Fin n) (Fin n) Nat` with nonnegative entries and hook sums `h_k = 1` for all k, `|mobius 0hat A| ≤ n.factorial` in the merge order with covers (i<j<k): a_ij+1, a_jk+1, a_ik−1, and (i<j): a_ij+1, a_jj+1, a_ii−1. Requires a `Finset` of matrices, a locally finite order instance on the subtype, the incidence-algebra Möbius function, and `Int` absolute value. No Tesler poset exists in Mathlib.

**Verdict.** NO CREDIT. Parked.

---

## 3. Deep route 344498 — subsquare extension for nonabelian Cayley tables

**Statement.** Evans–Mammoliti–Wanless, *Latin squares with maximal partial transversals of many lengths*, JCTA 180:105403 (2021), Conjecture 4.1: if X, Y ⊆ G with |G| = m, |X| = a > m/2 and |Y| = b > 2m/3, then there are a subgroup H ≤ G of order m and g, h ∈ G with X ⊆ gH and Y ⊆ Hh.

**Sources read.** arXiv:1911.05912 full-text: Conjecture 4.1, Examples 4.1–4.2 (sharpness at α=1/2, β=2/3), Theorem 4.1 (Ryser embedding), Theorem 4.2 (Kneser), Theorem 4.3 (abelian case), Theorem 4.4 (Olson), Theorem 4.5 (α/2+β>1), Lemma 5.1 (subsquares = cosets).

**My derivations (ordinary mathematics, no computation).**

1. *Normalisation.* Left-translate rows and right-translate columns to put 1 ∈ X and 1 ∈ Y; then X, Y ⊆ Z := XY and 1 ∈ Z, and the conclusion is invariant under these translations.
2. *The common difference set.* Set D := X⁻¹X = YY⁻¹. For x₁, x₂ ∈ X the b-subsets x₁Y, x₂Y of Z have |x₁Y|+|x₂Y| = 2b > m = |Z|, so they meet: x₁y = x₂y′ gives x₂⁻¹x₁ = y′y⁻¹ ∈ YY⁻¹. Symmetrically X⁻¹X ⊆ YY⁻¹. Hence D := X⁻¹X = YY⁻¹, and X, Y ⊆ D.
3. *Stabiliser dichotomy.* If XZ = Z then Z is a union of left cosets of ⟨X⟩; since |X| > m/2, Z is a single left coset of K := ⟨X⟩, so |K| = m. Moreover K g K ⊆ gK forces g ∈ N(K), so Z is also a right coset of K, giving the conclusion with H = K. Symmetrically ZY = Z gives H = ⟨Y⟩.
4. *The hard region.* So assume XZ ≠ Z and ZY ≠ Z. Olson's theorem (|AB| ≥ min(m, |A|+|B|−1) for A, B in a coset of a subgroup) applied to X and Z = XY forces |X|+|Z|−1 ≤ m unless X and Z fill a coset, i.e. a + m − 1 ≤ m, giving a ≤ 1 — contradiction, so Olson gives |X| + |XY| − 1 ≤ m, i.e. **a + 2b ≤ 2m**; symmetrically **2a + b ≤ 2m**. Together with a > m/2, b > 2m/3 this pins the hard region to
   m/2 < a < 2m/3, 2m/3 < b < m, a ≤ 2(m−b), b ≤ 2(m−a).
5. *Stabilisers are small.* In the hard case the left stabiliser of Z has order < m (else case 3 applies), and likewise the right stabiliser; so both are ≤ m/2.
6. *Smallest hard instances are excluded structurally.* (m, a, b) = (7,4,5) is the smallest. In A₄ the normal subgroup V₄ forces |XY| ≡ 0 mod 4 when X lies in one V₄-coset and |XY| ≥ 8 otherwise — so |XY| = 7 is impossible. In D₈ the normal ⟨r⟩ of order 4 forces |XY| ∈ {4,8}. In D₁₀ and S₃ the same coset arithmetic excludes 7. At m = 10, a = 6, b = 7, D₂₂'s prime-order rotation subgroup plus Cauchy–Davenport forces |XY| ≥ 11 for every split of X, Y across the two cosets. **No counterexample exists at these sizes.**

**Gap, stated precisely.** The abelian proof uses Kneser: in a finite abelian group, |AB| ≥ |A|+|B|−|H| where H is the stabiliser, and the abelian case closes because |X| > m/2 forces the stabiliser to have order m. In the nonabelian hard region Olson's 1/2-bound is *sharp* (there are genuine examples with |AB| = |A|+|B|−1 = m), so no contradiction arises. What is needed is a nonabelian Kneser-type theorem covering m/2 < |X| < 2m/3, 2m/3 < |Y| < m with |X|+2|Y| ≤ 2m and 2|X|+|Y| ≤ 2m — exactly the region where the two Olson inequalities are tight and the stabilisers are small. I found no such theorem in the source or in bounded search, and I have no argument for it.

**Lean endpoint.** For a group `G`, `X Y : Finset G`, `m : Nat` with `(X*Y).card = m`, `2*X.card > m`, `3*Y.card > 2*m`, produce a subgroup `H` with `H.toFinset.card = m`, a left coset `g • H.toFinset` containing X and a right coset `H.toFinset * {h}` containing Y. Needs `Finset` products, `Subgroup`, cosets, and invariance under translation.

**Verdict.** NO CREDIT. Parked with the gap above. The structural lemmas are elementary and would likely be judged routine by experts; I claim no novelty.

---

## 4. Deep route 360918 — common-card bound, bipartite vs non-bipartite

**Statement.** Bowler–Brown–Fenner (JGT 2010): a tree T and a unicyclic G on n vertices have at most ⌊n/2⌋+1 common cards, tight for n ≥ 44; the bipartite case is the last open one. Zwaneveld, arXiv:2311.16665, proves sufficiently large n and Theorem 7: 5n/6+2 cards determine bipartiteness.

**Source read.** arXiv:2311.16665: abstract, Conjectures 2–3, Theorem 4 (n ≥ 5000), Section 6 Theorem 7, and the three explicit families attaining ⌊n/2⌋+1 (Family 1 and Family 3 with n ≡ 1 mod 4; the diamond family of Figure 6).

**My analysis.** Every card of a bipartite graph is bipartite. So if G is bipartite and H is not, a common card forces H−w bipartite, i.e. w lies on *every* odd cycle of H. The number of such w can be as large as n (take H an odd cycle), so a bound of ⌊n/2⌋+1 cannot come from the H-side alone. It must come from counting isomorphism classes on the G-side: how many distinct (n−1)-vertex graphs can arise as G−v for bipartite G? That count is large in general (up to n classes), so the conjecture's content is a *joint* constraint — the two decks must share few classes.

**Gap, stated precisely.** Zwaneveld's 5n/6+2 comes from controlling vertices of degree ≤ 2 (small-cycle structure). To reach ⌊n/2⌋+1 one needs a threshold near n/2, which requires handling deleted vertices of degree ≥ 3: for such v the card G−v retains too much structure to be matched cheaply against a non-bipartite H−w. I found no argument controlling the degree-≥3 cards simultaneously with the odd-cycle constraint on H. The sharpness families show the bound cannot be improved below ⌊n/2⌋+1, so any proof must be exactly tight.

**Lean endpoint.** For `n ≥ 44`, `G H : SimpleGraph (Fin n)`, G bipartite, H not, the number of `SimpleGraph.Iso`-classes of (n−1)-vertex graphs occurring both as `G − v` and `H − w` is at most `n/2 + 1`. Requires vertex deletion, `SimpleGraph.Iso`, and a `Finset` of Iso-classes; the quotient-by-isomorphism encoding is the main formal obstacle.

**Verdict.** NO CREDIT. Parked.

---

## 5. Dead targets (source-owned, zero credit by rule)

- **382400** — arXiv:2507.12460, Hamilton decompositions of regular tripartite tournaments. The literal itself records the source's own status: *"Somewhat surprisingly, Granet gave a simple counterexample to this conjecture almost 10 years later."* The conjecture is **refuted in its own source**; there is no open statement. Formalising Granet's counterexample would be source-owned work.
- **356524** — arXiv:2210.10159, two-sided local limit for the diffusion approximation of tree profiles. The literal records corpus status *solved according to the source (as of October 2022)*, with the limit known via convergence to Brownian-excursion local time and its SDE. A source's own solution earns zero.

---

## 6. Parked targets (15) — one-line gaps

| ID | gap |
|----|-----|
| 363863 | No mechanism for a Z-interval restriction estimate at exponent 4 with q → 4/3; the additive-energy framework yields only the continuous analogue. |
| 366291 | Collinear-triple hypergraph carries Θ(n²) edges, so uniform O(√n)-colouring has Θ(n) expected monochromatic triples; first-moment/Lovász arguments fail at O(√n). |
| 360766 | Needs mass-transport or effective-resistance control for a union of two dependent forests on transitive transient graphs; the Z^d argument does not transfer. |
| 359765 | Needs configuration-model second-moment/switchings enumeration of joint regular decompositions with k = o(n). |
| 351797 | No visibility/Ramsey mechanism producing an island of unbounded size inside a single neighbourhood. |
| 339456 | Needs a lower bound covering *all* placements in dimension d; the source handles only special placements. |
| 341444 | Needs asymptotic enumeration of distinct entropy values beating the score-sequence count. |
| 334183 | Needs a claw-free structural decomposition plus a colouring bound matching the quadratic form. |
| 334728 | Needs a classification of tournament limits up to measure-preserving reparameterisation. |
| 319113 | Needs a construction of unbounded minimal graphs for a fixed attaching set (geometric measure theory). |
| 319212 | Threshold unspecified in the source; no algebraic characterisation of Leonard completely regular codes. |
| 367700 | Needs an explicit tree family with a matching N² log N lower bound; the source gives only O~(N²). |
| 364265 | General random Turán numbers for arbitrary bipartite F are beyond current container/absorption methods. |
| 317625 | McKay's fixed-length cycle control does not exclude growing-girth obstructions; no simultaneous bound on all cycle lengths. |
| 376715 | Requires an operator-algebra computation of split entropy in a chiral CFT; outside ordinary combinatorics. |

---

## 7. Network budget

- Search: **2 of 3 calls**, **6 of 9 queries** used. Search 001 (3 queries) confirmed the Evans–Mammoliti–Wanless and O'Neill identities; search 002 (3 queries) confirmed the three primary sources and found no resolution for any deep route. Responses saved complete: `searches/search-response-001.txt` (10 625 bytes, `428ff213…`) and `searches/search-response-002.txt` (13 113 bytes, `51f107be…`).
- GET guard: 4 successful hops (ordinals 1–4, seqs 1,3,5,7) of the per-ID cap 12 / global cap 48. Sources: arXiv 1911.05912, 2408.01513, 1702.00866, 2311.16665.
- Prior-art reconciliation: `historical-results-allowlist.json` has **zero** matches for all 20 IDs and all 20 source identifiers; `inherited-denials.json` has **zero** matches for all 21 checked URLs. No blocked key applies. Metadata selection is not scientific clearance — the gates above stand on their own analysis.

---

## 8. Declaration

No target in this lane reached the acceptance bar: no proof, no counterexample, no genuine survivor. The three deep routes are parked with precise gaps (per-step cancellation for 364214; nonabelian Kneser in the hard region for 344498; degree-≥3 card control for 360918). Two targets are dead by source ownership. Fifteen are parked with one-line gaps. **No `FULLCANDIDATE.md`, no `DORMANT-SOL-FORMAL-PLAN.md`.** Handback to root for adjudication.
