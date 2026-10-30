# Independent contribution review: integral staircase regular summand

**Verdict: SUBSTANTIAL, at a modest short-note scale. This verdict depends on the proof being valid.** The first independent proof gate recorded PASS with no repairs; this review re-derived the key steps but is not a second proof gate. The substantive content is the **abstract all-ring theorem**: (S^ρ_Z)^{⊗3} contains Z[S_N] as a direct summand. Its new mathematical consequence is a regular summand, hence every projective indecomposable with multiplicity at least dim D, for the primes 3 ≤ p ≤ 2m−1. In those characteristics the staircase is not a p-core, and I located no prior summand statement for them. The characteristic-0, characteristic-2 and p > 2m−1 parts of the package follow from prior work with little extra work (§3). Having a specified generator is a feature of the proof, not a separate contribution. The method is a short leading-monomial argument layered on Ikenmeyer's triangular uniqueness.

This is a substantive-contribution gate only. It makes no acceptance, count, manuscript, or worldwide-priority decision. The campaign count is untouched. Author of this review's original prose: Myeongjin Kang, no affiliation, CC BY 4.0; original code MIT (see [RIGHTS.md](RIGHTS.md)). Writes are confined to this directory. There were no subagents, shared edits, staging, commits, source removals, or uploads.

## 1. Frozen input and full target reviewed

`../fresh-algebra-discovery-r1/candidate.md` was read in full (151 lines, 17,969 bytes). Its SHA-256 is `6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179`, and its output manifest `79b0fcdd…dec9` (13,355 bytes) matches the brief. All other inputs, hashes and read extents are in [input-record.json](input-record.json).

**Full target reviewed, not narrowed.** The target covers every m ≥ 1, with N = m(m+1)/2, G = Sym(B) and z_m = v_R ⊗ v_R ⊗ v_C in L_m = (S^ρ_Z)^{⊗3}. Claim: the map δ_g ↦ g z_m has the explicit Z[G]-linear left inverse P_m = J^{-1} π_D q^B, with q(a,b,c) = δ_{a,c} f_{(a+b−1,a)}. The coefficient on e_w is exactly +1, where w(i,j) = (m+1−i, m+2−i−j). Hence, for every commutative unital ring A, A[G] → (S^ρ_A)^{⊗3} is split with the same generator. I review this as one package.

## 2. A clarifying reformulation (used for the comparison)

**The retraction is a single-monomial coordinate functional.** A retained output word e_{w∘g^{-1}} has a unique preimage triple. On each position the output (r,a) together with a = c fixes b = r+1−a. Write β(i,j) = m+2−i−j and col(i,j) = j, and put μ_0 = e_β ⊗ e_col ⊗ e_β. Then

  P_m(x) = Σ_g [g·μ_0](x) δ_g,

where [·] denotes a basis-monomial coordinate. This is not a defect. It shows that the theorem is exactly the following statement:

> (★) μ_0 occurs in z_m with coefficient +1, and no other translate g^{-1}μ_0 (g ≠ 1) occurs in z_m.

**An alternative proof of (★).** Suppose (β∘g, col∘g, β∘g) is a support monomial of z_m. The first and third layers give β∘g both row and column palettes, so β∘g = β by Ikenmeyer §5 (the candidate's nested-palette lemma). Hence g preserves antidiagonals. Row i must then receive the column values {1,…,m+1−i} under col∘g. We argue by induction on i, assuming g fixes rows 1,…,i−1 pointwise. The cell (i,j) lies on antidiagonal i+j, and its image lies on that antidiagonal in a row at least i. Its image column is therefore at most j. The palette forces column j, so g fixes row i.

Hence g = 1. The sign is (−1)^H · 1 · (−1)^H = +1. This route does not need the pair-sum square-deficit step: Ikenmeyer's uniqueness and a one-line triangular induction suffice. `comparison_checks.py` (C2) checks the induction exhaustively over the antidiagonal group for m ≤ 5; it is a sanity check, not a premise.

**Relation to Ikenmeyer.** Ikenmeyer's contraction uses tensors e_i ⊗ e_i ⊗ c_i, so the row and column layers carry the *same* letter τ. That is literally the a = c equality filter, and τ = β is forced. His coefficient carries θ = ∏ r! from symmetrisation, and his third layer uses generic vectors. The candidate's genuinely new step has two parts:

* it replaces the generic third layer by a second row polytabloid read through the column word;
* this kills the antidiagonal stabiliser H_A, so the monomial orbit is free and the factorial disappears.

## 3. What prior results already give, with little extra work

Each item below is my own derivation from cited results. I do not attribute it to the cited authors. It is offered so that the contribution is not over-credited.

**(a) Integral version of Harman–Ryba Thm 2.4 for the staircase.** For h ∈ H_R (the row group), the β-coordinate of h·v_C is ±δ_{h,1}. This holds because β∘h has row palettes, Ikenmeyer's uniqueness forces β∘h = β, and β is injective on rows. Hence Z[H_R]·v_C is a Z-split, H_R-split summand of Res_{H_R} S^ρ_Z (C1 checks this for m ≤ 4). Inducing gives

  M^ρ_Z ⊗ S^ρ_Z ≅ Ind_{H_R}^G Res_{H_R} S^ρ_Z ⊇ Z[G], split.

HR's own proof of Thm 2.4 is a Frobenius-characteristic identity (HR p. 508) and is not integral, but this integral version takes a few lines. Equivalently, it follows from a Z-free Specht filtration of the restriction together with relative Z-injectivity of free modules.

**(b) Characteristic 0.** I21 §2.1 plus HR Thm 2.4 gives this (credited in the candidate §5).

**(c) Characteristic p with ρ a p-core, i.e. p = 2 or p > 2m−1.** The staircase hook lengths are exactly the odd numbers 1, 3, …, 2m−1 (C3). So ρ is a p-core iff p = 2 or p > 2m−1, and then S̄ = S^ρ_{F_p} is simple and projective (HR Lemma 3.2(3)). In that case S̄ ⊗ − splits every short exact sequence, since projective implies injective for group algebras. So S̄^{⊗3} ≅ ⊕_D [S̄⊗S̄ : D] (S̄ ⊗ D).

The composition multiplicities of S̄ ⊗ S̄ dominate those of M̄^ρ, by the complex I21 inclusion and Brauer characters. Hence S̄^{⊗3} ⊇ S̄ ⊗ M̄^ρ ≅ Ind_{H_R}^G Res S̄ ⊇ F_p[G], using (a) reduced mod p. This is HR's §3 mechanism, extended from "every PIM occurs" to "regular summand". It takes about a paragraph. The candidate is therefore right that HR Remark 3.3 does not *state* regular multiplicities, but supplying them at p = 2 is little additional work.

**(d) Generic tensor powers.** Bryant–Kovács, *Tensor products of representations of finite groups*, Bull. LMS 4 (1972) 133–135, [DOI 10.1112/blms/4.2.133](https://doi.org/10.1112/blms/4.2.133), is relevant background. As seen at abstract/preview level only, their result is: if no non-identity element acts as a scalar on V, then the regular module is a direct summand of **some** tensor power of V, over a field. For S^ρ_K this already gives a free summand in some unspecified power in every characteristic. The candidate's content is therefore the **uniform exponent 3**, for all m and all p, together with an integral form. The qualitative "eventually free" phenomenon is classical. I did not read the full Bryant–Kovács text; the candidate does not cite it and should.

**What is *not* obtained by (a)–(d).** For odd primes p ≤ 2m−1, S̄^ρ is not projective. Its dimension has p-part strictly below |G|_p, because the hook length p occurs. The splitting argument in (c) therefore fails. Route (a) would need M^ρ, or some module whose tensor with S contains a free summand, to be a summand or a suitable unit-preimage quotient of S ⊗ S. The pinned map gives only the scalar ∏ r!, which is not a unit at p ≤ m. I found no published or pinned route around this, and the candidate's third layer is exactly what removes it. This is the real integral and modular obstruction, and the candidate overcomes it.

## 4. Comparative statements (exact hypotheses)

| Source | Hypotheses | Conclusion | Relation |
|---|---|---|---|
| Harman–Ryba 2023, Thm 1.1 (alco.267, p. 507) | complex | cube contains every S^λ | inherited support |
| HR Thm 2.4 (p. 508) | any μ, complex | M^μ ⊗ S^μ ⊇ M^{C(μ)}; C(ρ) = (1^N) | with I21 gives complex regular summand; integral form easy, §3(a) |
| HR §3 second proof + Rem. 3.3 (pp. 509–510) | char 2, alg. closed; ρ a 2-core | every PIM is a direct summand of the cube | inherited occurrence; regular multiplicity at p=2 easy, §3(c) |
| BBS 2021, p. 1029 Strengthened Saxl; §5, Thm 5.2 (pp. 1047–1048) | char 2 | conjectures every PIM in the **square**; height-zero positivity | open square problem, not addressed by candidate |
| Bessenrodt–Bowman arXiv:2202.03066v3, §3, Thm 3.7 | char 0 / 2-projective characters | sym − alt multiplicity of [ρ] | different target |
| Ikenmeyer 2015 §§4–5 | complex; rows/columns/generic third layer | τ = β unique; coefficient θ·(±1)·det | supplies uniqueness and the a = c filter in essence |
| Pinned cyclic `dominance.tex` lines 126–192 | complex | Q(v_R⊗v_R) = ±∏ r! · t_m | factorial obstruction the candidate removes |
| I21 §2.1 | complex | C[G](v_R⊗v_R) ≅ M^ρ | inherited |
| Bryant–Kovács 1972 (preview only) | field; no non-identity scalar element | regular summand in **some** tensor power | qualitative antecedent; not exponent 3, not integral |

## 5. Decision rationale

**For SUBSTANTIAL**

* The abstract theorem strengthens a 2023 published result (HR Thm 1.1 and Rem. 3.3) in a direction HR's methods cannot reach: non-core odd characteristics, regular multiplicities, and an integral form uniform in m.
* For odd 3 ≤ p ≤ 2m−1 it gives the first staircase-cube summand statement I could locate (bounded search, §7).
* The obstruction it removes, a non-unit factorial on the only available route, is real and not an artefact of presentation.
* The statement is clean and natural for the modular Saxl programme of BBS.

**Against, and why I did not choose TECHNICAL.** Given Ikenmeyer, the proof is short (§2), and three of the four characteristic regimes are near-routine (§3). If the package were judged only by p = 0, p = 2 and p > 2m−1, TECHNICAL would be right. The decisive regime is 3 ≤ p ≤ 2m−1 together with the integral form, where no route of comparable length is known to me. My confidence in the SUBSTANTIAL call is **moderate**. It is a short-note contribution, not a structural advance on the Saxl square.

**Not KNOWN/DUPLICATE.** In the inspected sources, and within the bounded search, no source states an integral or all-characteristic regular (or even all-PIM) summand of the staircase cube for odd p.

**Not UNRESOLVED.** The remaining uncertainty is ordinary literature uncertainty, bounded in §7. It is not a gap in the comparison.

**Specified generator vs abstract theorem.** The choice z_m = v_R ⊗ v_R ⊗ v_C carries no independent novelty beyond witnessing the abstract theorem. The abstract statement is what should be credited.

## 6. Points for proof and manuscript reviewers (none blocking)

1. **Identification of S_A.** The candidate defines S^ρ_A := A ⊗ S^ρ_Z. Over a field K this equals James's Specht module (the K-span of polytabloids in M^ρ_K) because S^ρ_Z is a pure sublattice of M^ρ_Z, by the standard-polytabloid basis theorem. The manuscript should state this, so that its modular corollaries refer to the usual S^ρ_K. This does not affect the theorem as stated.
2. **Splitting fields.** "P(D) with multiplicity ≥ dim D" needs a splitting field (true for F_p and S_N). The regular-summand statement itself needs nothing.
3. **Presentation recommendations** (not required for this verdict):
   * state the abstract theorem and its odd-p modular corollary explicitly;
   * explain why the p-core cases (p = 2, p > 2m−1) were already accessible and the non-core odd primes were not;
   * cite Bryant–Kovács 1972 and note the integral form of HR Thm 2.4;
   * consider the single-monomial formulation (★) as a shorter proof or a remark.
4. No mathematical concern was found with the proof as reconstructed in §2. This is consistent with the first proof gate.

## 7. Search record and bounds

Primary passages read (exact extents in [input-record.json](input-record.json)):

* Harman–Ryba, entire text;
* Ikenmeyer, lines 260–430 (§§4–5);
* BBS lines 290–330 and 1300–1385, plus a keyword scan;
* Bessenrodt–Bowman lines 320–480 and 1555–1580, plus a keyword scan;
* pinned `dominance.tex` in full and `specht-tools.tex` lines 40–100;
* I21 lines 1–99 (including §2.1, lines 45–59).

Web searches run in this review:

1. `Saxl conjecture positive characteristic tensor cube staircase projective summand odd prime` (extended);
2. `tensor power Specht module contains free summand regular module symmetric group modular "free summand"` (extended);
3. `tensor products of Specht modules positive characteristic projective summands staircase 2-core Kronecker modular 2024 2025`;
4. `"Saxl" staircase tensor square "regular representation" OR "regular module" contains integral Specht lattice`;
5. `Bryant Kovács free Lie algebra tensor power faithful module free summand modular group algebra`;
6. `tensor product of modules contains group algebra as direct summand criterion …`;
7. `Bryant Kovács 1972 "Tensor products of representations of finite groups" …`;
8. `Saxl conjecture odd characteristic p-modular staircase tensor square projective cover Specht 3-modular`.

One further extended query, on Harman–Ryba follow-ups in characteristic p, failed because of a tool session limit and was not completed. arXiv:2512.15035 (Lee, a claimed proof of the Saxl *square*) was opened. Its abstract page reports that it was **withdrawn** on 20 Dec 2025 for mathematical gaps; it makes no integral, regular or cube claim. Kua–Lim arXiv:2603.11533 and 2607.16626 (tensor products for F S_p, modulo projectives) surfaced as unrelated to this target.

**Not done:** citation-index (MathSciNet/zbMATH) forward search of Harman–Ryba, the full text of Bryant–Kovács, and integral representation texts (Curtis–Reiner, Plesken) for a general "free summand of a cube" criterion. The negative finding is bounded to these sources and queries and does not establish priority.

## 8. Own checks

`python3 -I -B comparison_checks.py` writes `comparison-checks.txt` (ALL PASS):

* C1: the integral restriction lemma, over the full row group, for m ≤ 4;
* C2: the antidiagonal-stabiliser induction of §2, exhaustively for m ≤ 5 (34,560 elements at m = 5);
* C3: staircase hook lengths are exactly the odd numbers ≤ 2m−1, for m ≤ 12.

These are finite sanity checks of comparison arguments, not evidence of contribution or of the all-m theorem. The GLM implementation, the candidate's finite controls and the proof gate's controls were not used as contribution premises.
