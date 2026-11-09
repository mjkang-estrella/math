# Independent adversarial review: MathDB 347230 (with companion 347231)

**Lane:** hetyei-review-r1 (Claude Opus 5.5).
**Date:** 2026-11-05.
**Status:** this is a review only, not an acceptance, and carries zero credit.

**Restrictions observed.** No Lean, lake, leanchecker or SAT/ILP binaries were run. Every computation was one capped foreground `python3 -I -B` run. Nothing was written outside this lane. No child agents, no git, and none of the discovery lane's scripts were imported or run.

**Overall recommendation: PROCEED for 347230. EXCLUDE 347231 as a separately credited record.**

| Gate | Verdict |
|---|---|
| A. Statement fidelity and misprint reading | **PASS** |
| B. Independent mathematics | **PASS** |
| C. Prior art | **QUALIFIED_PASS** |
| D. Significance and exclusions | **QUALIFIED_PASS** for 347230; 347231 not separately creditable |
| E. Lean route | **QUALIFIED_PASS** |

---

## Inputs and hash binding

* **Discovery lane `expanded-corpus-r240`.** All 249 files were hashed before (`hashes-before-r240.json`) and after (`hashes-after-r240.json`). There are 0 differences, and both files have sha256 `4480d034…ebc4`. The lane's `CANDIDATE.md` sha256 is `25092a9c236c9f3c0b2ffc728d44508dd321eb1f5c4d76d40c3869859aff1e34`, matching the task.
* **Own downloads.** Each went into a fresh directory under `dl/`, with a receipt `*.receipt.json` next to it. No receipt was overwritten, nothing was retried, and TLS verification stayed on.
  * arXiv abstract page 2007.07362v1 (200). It lists exactly two versions: v1 of 14 Jul 2020 and v2 of 19 Jul 2020.
  * arXiv e-print LaTeX sources for v1 (200, sha `b12e7d21…`) and v2 (200, sha `075862b3…`), unpacked safely into `src-v1/` and `src-v2/`.
  * Ehrenborg–Readdy, *Coproducts and the cd-index*, from `www.ms.uky.edu/~jrge/Papers/Coproduct.pdf` (200). Its sha256 `0df8dd40…1282` is byte-identical to the lane's copy.
  * Springer DCG page: **303 cross-host redirect to idp.springer.com (cookie authorisation), not followed and not retried.** For the DCG version I therefore used the lane's hash-bound HTML copy (sha `cf61870b…`).
  * OpenAlex (3 calls) and GitHub/Lean Pool (7 calls, spaced).
  * The arXiv author pages `arxiv.org/a/hetyei_g_1(.atom2|.html)` returned 404, so I stopped there.

---

## Gate A: statement fidelity (PASS)

### Source identification

G. Hetyei (Gábor Hetyei), *The type B permutohedron and the poset of intervals as a Tchebyshev transform*.
* arXiv:2007.07362, v1 and v2.
* Discrete Comput. Geom. 71 (2024) 918–944, doi 10.1007/s00454-023-00490-4. Received 20 Dec 2021, published 26 Feb 2023.

In arXiv numbering this is Section 5, "Interval transforms of the second kind". In DCG numbering it is Section 6.

My `scripts/secdiff.py` shows the section is **identical in v1 and v2** except for one dangling fragment. v1 ends Corollary 5.13 with "Furthermore, if", which v2 removed.

### Quotations

Line references below are to v2 `src-v2/btch-v02.tex`; the v1 lines are given in brackets.

* **Conventions (l.196–201, l.1017–1018).**
  * Υ_P = Σ_S f_S u_S, where u_i = b for i ∈ S and a otherwise.
  * Ψ_P is Υ_P with a replaced by e = a − b.
  * Coproduct (Def. 4.6, l.964–971): Δ(u₁⋯uₙ) = Σᵢ u₁⋯u_{i−1} ⊗ u_{i+1}⋯uₙ.
  * u* is the reversed word (l.978–980).
  * Q⟨a,b⟩ₙ is the span of ab-words of length n (l.1242–1244).
* **Def. 5.1 (l.1115–1120).** Î₂(P) is the multiset, over x ∈ P, of the subposets {[y,z] ∈ I(P) : [x,x] ⊆ [y,z]}.
* **Cor. 5.3 (l.1133–1138).** For graded P these are the intervals [[x,x],[0̂,1̂]].
* **Def. 5.4 (l.1140–1153).** The total ab-index is Ψ_{Î₂(P)} = Σ_{x∈P} Ψ_{[[x,x],[0̂,1̂]]}. The source prints "Σ_{u∈P}", a harmless typo.
* **Prop. 5.5 (l.1156–1163).** [[x,x],[0̂,1̂]] ≅ [0̂,x]* × [x,1̂].
* **Def. 5.6 = DCG Def. 31, the mixing operator (l.1169–1184; v1 l.1126–1141).**

  M(u,v) = Σ_{r,s∈{1,2}} Σ_{n−r−s−1 even} M_{r,s,n}(u,v), with

  M_{1,2,2}(u,v) = u·a·v;
  **M_{2,1,2}(u,v) = u·b·v** (l.1179; v1 l.1136);
  M_{1,s,n+1}(u,v) = Σ_u u₍₁₎·a·M_{2,s,n}(u₍₂₎,v);
  M_{2,s,n+1}(u,v) = Σ_v v₍₁₎·b·M_{1,s,n}(u,v₍₂₎).

  The DCG HTML has the same text, `M_{2,1,2}(u,v)= u\cdot b\cdot v` (raw HTML l.1359; lane text l.278–282).
* **Eq. (5.1) (l.1189–1192).** Ψ_{P×Q} = M(Ψ_P, Ψ_Q), citing ER Thm 9.2.
* **Thm 5.7 = DCG Thm 32 (l.1197–1206).** Ψ_{Î₂(P)} = 𝓘₂(Ψ_P), where 𝓘₂(u) = u + u* + Σ_u M(u₍₁₎*, u₍₂₎).
* **Cor. 5.8 = DCG Cor. 33 (l.1235–1239).** If u ∈ Q⟨a,b⟩ₙ and u* = −u, then I₂(u) = 0.
* **Def. 5.9 = DCG Def. 34 (l.1245–1251).** Symmetric means u* = u, giving S_Q⟨a,b⟩ₙ. Antisymmetric means u* = −u, giving **A_Q⟨a,b⟩ₙ**.
* **Prop. 5.10 = DCG Prop. 35 (l.1252–1260).** dim A = 2ⁿ⁻¹ − 2^⌊(n−1)/2⌋ and dim S = 2ⁿ⁻¹ + 2^⌊(n−1)/2⌋.
* **Lemma 5.11 = DCG Lemma 36 (l.1279–1297).** If u is an I₂-eigenvector, then so is 𝓛(u) := (a−b)u + u(a−b), with the same eigenvalue.
* **Prop. 5.12, Cor. 5.13 = DCG 37, 38 (l.1301–1328).**
* **Conj. 5.14 = DCG Conj. 39 (l.1344–1347; v1 l.1301–1304; DCG text l.335).**

  > For each n ≥ 1, the kernel of I₂ : Q⟨a,b⟩ₙ → Q⟨a,b⟩ₙ₊₁ is A_Q⟨a,b⟩ₙ.
* **Conj. 5.15 = DCG Conj. 40 (l.1349–1354; DCG l.337).**

  > For each n ≥ 1 a generating set of S_Q⟨a,b⟩ₙ, consisting of eigenvectors only may be found by taking all possible n-fold compositions of the pyramid operator Pyr and of the lift operator 𝓛, and applying it to 1.
* **Additional source claims used as checks.**
  * The "obvious" symmetry M(u,v) = M(v,u) (eq. Mswap, l.1440–1444) and M(1,1) = c (l.1445–1448).
  * Prop./Thm on I₂(cⁿ) (l.1655–1690). These print the hypothesis "2r + Σk = n − 1"; with degree n in its place, the coefficient formulas hold.

The macro `\II` is I₂ and `\IIab` is 𝓘₂ (l.42, l.47). From l.1229 onwards the source uses I₂ for the linear operator 𝓘₂.

### Which subspace is A

**A_Q⟨a,b⟩ₙ = {u ∈ Q⟨a,b⟩ₙ : u* = −u}**, the antisymmetric part (Def. 5.9).

The printed codomain "Q⟨a,b⟩ₙ₊₁" is a slip carried over from the first-kind transform, which raises rank. 𝓘₂ preserves degree, since deg M(x,y) = deg x + deg y + 1, and [0̂,x]* × [x,1̂] has the rank of P. So the conjecture is about ker(I₂|_{Q⟨a,b⟩ₙ}).

The re-indexing caveat does not change the conclusion. If n were read as rank rather than degree, the failure would occur at "n = 6" instead of 5.

### The misprint: which reading is intended

Ehrenborg–Readdy, J. Algebraic Combin. 8 (1998), Definition 9.1 (lane text of the byte-identical PDF, l.1062–1071), reads:

M_{1,2}(u,v,2) = u·a·v, **M_{2,1}(u,v,2) = v·b·u**.

The index set is n ≡ r+s+1 (mod 2) (l.1048), the same as Hetyei's. The convention is stated at l.1081–1083 and l.1092–1093:
* "When r = 1 each summand begins with a u-piece, while when r = 2 the summands begin with a v-piece. … s = 1 says that each summand ends with a u-piece."
* There is "an a between an adjacent u-piece and v-piece (reading left to right), otherwise … a b".

So M_{2,1,2} must begin with a v-piece, end with a u-piece, and have b between them, i.e. v·b·u. The printed u·b·v also contradicts Hetyei's own recursion, where r = 2 summands start with v₍₁₎·b.

**Mathematical decision (own code, `logs/validate-5.log`, `logs/srcvalues-6.log`):**

| Check | ER v·b·u | printed u·b·v |
|---|---|---|
| ER Thm 9.2 / Hetyei eq. (5.1): Ψ(P×Q) = M(Ψ_P, Ψ_Q), 70 poset pairs | 0 mismatches | 69 mismatches; M(a,1) = aa + 2ab but Ψ(C₂×C₁) = aa + ab + ba |
| Thm 5.7/32 against brute-force Î₂, 29 posets (chains, B₁–B₄, 3–6-gons, square pyramid, prism, cube, octahedron, 12 random graded) | 0 mismatches | 9 mismatches (e.g. prism, cube, octahedron) |
| Thm 5.7/32 against brute-force Î₂ on all doubled chains, which span Q⟨a,b⟩ₘ, m ≤ 5 | 0 mismatches | 2, 4, 12, 28 mismatches at m = 2..5 |
| M(u,v) = M(v,u) (eq. Mswap) | holds | 110 failures |
| Cor. 5.8/33: I₂(w*) = I₂(w), \|w\| ≤ 6 | holds | 98 failures; A ⊄ ker, e.g. I₂(ab − ba) = 2ab − 2ba |
| I₂(M(u,v)) = M(I₂u, I₂v) (Prop. 5.12 ⇒ Cor. 5.13) | holds, 49/49 | 48/49 fail |
| Boolean eigen-relation, I₂(cⁿ) coefficient formulas | hold | hold (blind to the misprint) |

**Verdict.** The intended reading is ER's v·b·u, which is the reading under which the source's proved results are true. Under that reading the conjecture **fails at n = 5**.

Under the misprinted reading the conjecture also fails, from n = 2 on (ker = 0 ≠ A), but that is a misprint artefact and should claim no credit. The two readings agree on chains, Boolean algebras and cⁿ, which plausibly explains why the misprint went unnoticed.

The doubled-chain pinning matters here. At degree 5 the poset-defined transform u ↦ Ψ_{Î₂} on a spanning set of posets coincides with 𝓘₂ (ER reading). So **the n = 5 refutation is a statement about Hetyei's poset construction itself and does not depend on how the misprint is resolved.**

### MathDB literals

* **347230** (`raw/347230.jsonl`) matches Conj. 5.14/39, with "the specified subspace" for A, which the source fixes as the antisymmetric part. It is faithful.
* **347231** (`raw/347231.jsonl`) **misdefines 𝓛 as u ↦ (a−b)u.** That is ER's variant mentioned at l.1338–1339. The source's 𝓛 in Conj. 5.15 is Lemma 5.11's (a−b)u + u(a−b). The refutation below is robust to either 𝓛, but the discrepancy must be recorded.

---

## Gate B: independent mathematics (PASS)

**Implementation.** `scripts/review_math.py` is my own code, written from the source definitions:
* the ER coproduct and Def. 5.6, with a switch for the base-case reading;
* Thm 5.7 for 𝓘₂;
* the ab-index from flag f-vectors via Ψ = Σ f_S ∏(b or a−b);
* a brute-force Î₂ built directly from the poset of intervals, ordered by inclusion;
* exact Fraction linear algebra.

Logs are in `logs/`.

**Validation.** See Gate A. The validation includes full operator pinning on doubled chains for degree ≤ 5. The ab-indices of the 2^m doubled chains have rank 2^m.

**Kernel dimensions** (`logs/kernel-1-6.log`, `logs/kernel-7-7.log`):

| n | dim A | ER: rank / dim ker / dim(ker ∩ S) | conjecture (ER) | printed: dim ker |
|---|---|---|---|---|
| 1 | 0 | 2 / 0 / 0 | holds | 0 |
| 2 | 1 | 3 / 1 / 0 | holds | 0 (A ⊄ ker) |
| 3 | 2 | 6 / 2 / 0 | holds | 0 |
| 4 | 6 | 10 / 6 / 0 | holds | 0 |
| **5** | **12** | **19 / 13 / 1** | **fails** | 0 |
| 6 | 28 | 34 / 30 / 2 | fails | 0 |
| 7 | 56 | 65 / 63 / 7 | fails | 0 |

A ⊆ ker holds for every n under ER, and fails for n ≥ 2 under the printed reading. This reproduces the lane's 0, 1, 2, 6, 13, 30, 63. I did not check the lane's mod-p bounds for n = 8, 9; the refutation does not need them.

**Certificate** (`logs/cert.log`). I transcribed u from CANDIDATE.md; it is identical to `outputs/hetyei-certificates-v2.json`.
* u has 20 terms, all of degree 5, with u* = u and u ≠ 0.
* **Under ER, I₂(u) = 0.**
* Each I₂(w) has coefficient sum 64.
* Under the printed reading, I₂(u) = −8abaab + 8ababa + 8baaab − 8baaba ≠ 0.
* Independently, ker(I₂|_{S₅}) is 1-dimensional and spanned by −u. So u is the unique kernel direction outside A at n = 5, up to scalar.

A minor erratum in the dossier: the "1280 unit terms" in CANDIDATE.md §2 is 20 × 64, which does not weight by |coefficient|. Weighted, the count is 1536. This does not affect the result.

**347231** (`logs/eigen-5.log`, `logs/misc.log`).
* **Spectrum.** All eigenvalues of I₂ on Q⟨a,b⟩ₙ, n ≤ 5, are rational (0 and powers of 2), and I₂ is diagonalisable.
* **Eigenvectors inside Sₙ.** They span 2/2, 3/3, **5/6**, 7/10 and 13/20 for n = 1..5, matching the lane. At n = 3: λ = 2 gives 1, λ = 4 gives 2, λ = 8 gives 1, λ = 16 gives 1.
* **The n = 3 mechanism.** I₂(aab) = aaa + 4aab + 3aba + 2abb + 3baa + 2bab + bba. So I₂(aab + baa) ∉ S₃. Hence I₂(S₃) ⊄ S₃, and no basis of S₃ consists of I₂-eigenvectors. The lane's α-argument is correct.
* **Lemma 5.11/36 is false.** Ψ(B₃) = aa + 2ab + 2ba + bb has eigenvalue 8, but I₂(𝓛Ψ(B₃)) − 8𝓛Ψ(B₃) = −12aba − 12abb + 12baa + 12bab ≠ 0. 𝓛(Ψ B₃) is not an eigenvector even modulo A₃: the palindromes aaa and aba would force λ = 8 and λ = 5 at once. 𝓛(Ψ B₁) and 𝓛(Ψ B₂) are eigenvectors.
* **Source 𝓛.** The compositions span Sₙ for n ≤ 5, but are not all eigenvectors from n = 3. The first failure is 𝓛∘Pyr∘Pyr(1) = 𝓛(Ψ(B₃)), exactly the Lemma 36 counterexample. There are 1, 5 and 16 non-eigenvectors at n = 3, 4, 5.
* **MathDB 𝓛 = (a−b)u.** The compositions are non-symmetric and non-eigen already at n = 2.

So Conj. 5.15/40 fails under every reading checked: the literal one, source or MathDB 𝓛, and "eigenvector modulo A".

---

## Gate C: prior art (QUALIFIED_PASS)

* **OpenAlex** W3043671903, one work merging the arXiv and DCG versions, has 3 citing works:
  * Galashin, *P-associahedra* (2023);
  * Ferroni–Riccardi, *Eulerian posets and Z-polynomials* (2026), which uses the poset of intervals for toric h, not I₂;
  * Mir-Fuentes et al., on fuzzy numbers (2026).

  None concerns I₂, its kernel or its eigenvectors (abstracts checked).
* **Later Hetyei works.** OpenAlex author A5089863827 has 14 works since 2020-07 (knots, hypermaps, nestohedra, noncrossing partitions, Catalan–Spitzer). None concerns the interval transform.
* **Errata.** None found: OpenAlex lists no correction, and the DCG page copy has no erratum or correction text. The Definition 31 misprint survives into the version of record.
* **Ehrenborg–Readdy literature.** The mixing operator's base case is as quoted above. I found no later correction of ER Def. 9.1, and my own computation confirms ER Thm 9.2 with v·b·u.
* **Registries.**
  * Lean Pool HEAD `01db1d7049cf9668bda1e9e106875ee1278b43e6` (2026-10-07; same as the lane's snapshot): `LeanPool/projects.yml` and `candidates/discovered.yml` have no hit for Hetyei, 2007.07362, 347230/347231, interval transform, mixing operator or Tchebyshev. I listed `candidates/`.
  * GitHub repository search "hetyei": 0 results.
  * GitHub repository search "cd-index"/"ab-index" poset: only unrelated results.
  * GitHub issue search "2007.07362" OR "347230" OR "interval transform of the second kind": only number collisions.
* **Limits.**
  * Crossref, Semantic Scholar, the arXiv search API, ScienceDirect and DBLP are denied.
  * I had no access to Springer's live page (cookie redirect), Google Scholar, MathSciNet or zbMATH reviews.
  * The arXiv author listing returned 404.
  * Citing-work coverage is OpenAlex-only. I did not re-query the Omega registry; the lane's Omega screen at HEAD 046c7ac2 was clean.

---

## Gate D: significance and exclusion screen (QUALIFIED_PASS for 347230)

**Not a source-formula evaluation or source-data contradiction in the 340386 / 347642 / 355701 sense.** Those exclusions were (ledger l.12173, l.12177, l.11267):
* a closed weight formula already printed in the source and directly evaluated;
* a contradiction with the source's own printed table;
* the next catalogue entry of the source's own GAP search.

Here the source gives no formula, table or procedure for the kernel, and none of its printed results contradicts Conj. 39. The refutation needs a new object, an explicit symmetric kernel element outside A, and that object exists only from n = 5. The deficiency then grows: 1, 2, 7 at n = 5, 6, 7. That makes it a structural failure of the conjecture rather than an edge case.

It matches the qualifying profile of small exact computer-found counterexamples to a published conjecture (346167, 332037, 369421): a stated conjecture in a 2024 DCG paper, refuted by a 20-term integer certificate.

**Not a wording or misprint artefact.**
* The failure holds under the intended reading, the only one under which Thm 32 and Cor 33 are true.
* At n = 5 it is pinned to Hetyei's poset construction independently of the mixing-operator definition.
* The misprinted reading gives a different, trivial failure, which should not be credited.

**Not a consequence of a false source lemma.** Conj. 39 does not depend on Lemma 36.

**Qualification on significance.** The certificate comes from a mechanical 32×32 rank computation, at the first degree where hand checking is impractical. The source shows no evidence that the author computed beyond small degrees. Root should weigh this "modest computation" aspect. I judge it consistent with the credited precedents above, not with the exclusions.

**347231: EXCLUDE as a separate credit.** It is the same source family, and its failure is elementary: I₂(aab + baa) is not symmetric, a hand computation in degree 3. The eigenvector clause first fails exactly at 𝓛(Ψ(B₃)), a counterexample to the source's own Lemma 36, on which Conj. 40 rests.

The stronger "no eigenvector generating set of S₃ exists" is also immediate from I₂(S₃) ⊄ S₃. The MathDB literal also misdefines 𝓛. Lemma 36's failure and the S₃ non-invariance can be reported as remarks in the 347230 paper.

**Recommendation: credit 347230 only (PROCEED to Lean). 347231: EXCLUDE (same family; elementary; rests on the source's false Lemma 36).**

---

## Gate E: Lean route (QUALIFIED_PASS)

**Cheapest literal endpoint.** This is essentially the lane's draft design, which I checked line by line against my implementation.

**Definitions:**
* `Word := List Bool`
* `ABPoly := Word →₀ ℚ`
* `star := Finsupp.lmapDomain List.reverse`
* `deg n := Finsupp.supported {w | w.length = n}`
* `anti n := deg n ⊓ ker(star + id)`
* the computable `cop`, and `Mrs` with ER's base cases
  * In the draft, `| true, false, 2, u, v => [(v ++ [true] ++ u, 1)]` is correct for ER.
  * Its recursion uses `Mrs true s (n+2) p.2 v` for r = 1 and `Mrs false s (n+2) u p.2` for r = 2, which is correct.
  * The parity filter `inIndex` is correct.
* `I2w w = [(w,1),(w.reverse,1)] ++ Σ Mw (p.1.reverse) p.2`, which is correct.
* `I2 := Finsupp.linearCombination`.

**Statements:**
* `KernelConjecture : ∀ n ≥ 1, deg n ⊓ ker I2 = anti n`. This faithfully renders "kernel of I₂ on Q⟨a,b⟩ₙ".
* Negation `not_KernelConjecture` via `uCert`, as drafted.

**Required changes before formal investment:**
1. **Truncation fidelity.** `Mw` sums n only up to |u|+|v|+2. Either prove `Mrs r s n u v = []` for n > |u|+|v|+2 (induction: each step strictly shortens one argument), or state M as the full ER sum and derive the truncation. The draft mentions this lemma but does not state it. Without it, a reviewer cannot match `Mw` to Def. 31's unbounded sum.
2. **Computation tactic.** The 1536-term check `check_I2u` should use `decide +kernel` or an equivalent kernel `rfl` with `Bool`/`Int` reduction. Plain `decide` may exceed recursion or heartbeat limits. `native_decide` is not allowed.
3. **Bridge proofs.** Fill the 9 `sorry`s. Six are for 347230: `I2_toPoly`, `toPoly_eq_zero_of_coeff`, the membership step in `I2_uCert`, `uCert_deg`, `star_uCert` and `uCert_ne_zero`. Three are the 347231 helpers `alpha_symm`, `s0_symm` and `alpha_I2_s0`, needed only if those are kept. All are routine Finsupp bookkeeping.
4. **Optional robustness lemma.** With the printed base case, `I2_printed(ab − ba) = 2ab − 2ba ≠ 0`. This formally covers "the conjecture fails under either reading" for a few lines. Mark it as non-credited.
5. **347231 (not recommended for credit).** A literal endpoint would need Pyr, the composition set, and both the source and MathDB 𝓛. The draft's `EigenGeneration` is a valid consequence of Conj. 40 under any 𝓛, so ¬EigenGeneration ⇒ ¬Conj40. That implication should be stated and proved explicitly.

**Cost.** Small: about 200–400 lines, one formalisation round. The main risk is the elaboration cost of the kernel `decide` on a 1536-term list. Everything is finite, over ℚ and ℤ, with no analysis.

**Assessment of the draft.** The definitions are faithful to ER Def. 9.1 and Thm 32 under the intended reading. It is uncompiled and has 9 `sorry`s. Items 1–3 above are mandatory.

---

## Files in this lane

**Scripts** (`scripts/`):
* `review_math.py` (all mathematics)
* `fetch.py`, `unpack.py`, `secdiff.py`, `grep.py`, `jsonpick.py`, `ls.py`
* `hashbind.py`, `hashcompare.py`
* `pdfpage.py`, which failed because pypdf is not installed; this is recorded and nothing depends on it

**Logs** (`logs/`):
* `validate-5.log`, `kernel-1-6.log`, `kernel-7-7.log`, `cert.log`, `srcvalues-6.log`, `eigen-5.log`, `misc.log`

**Downloads** (`dl/*/`): all with receipts.

**Unpacked sources:** `src-v1/`, `src-v2/`.

**Hashes:** `hashes-before-lane.json`, `hashes-before-r240.json`, `hashes-after-r240.json`, and `hashes-final-lane.json` (my own outputs).
