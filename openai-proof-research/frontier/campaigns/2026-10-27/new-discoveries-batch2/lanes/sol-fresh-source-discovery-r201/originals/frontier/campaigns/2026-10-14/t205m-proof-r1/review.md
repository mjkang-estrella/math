# T205M independent full-scope proof gate, round 1

Reviewer role: independent proof gate only. No contribution, novelty,
acceptance or count verdict is given here. Original prose CC BY 4.0;
reviewer code MIT. Uploads and publication remain stopped.

## Verdict

**PASS_FULL_T205M.**

I found no required proof gap. Every quantifier of the frozen statement
(`scope205m.md`, SHA256 `3eb9d790…afb64f6`) is proved from the stipulated
pinned source statements, Kirillov's published rigged-configuration formula,
the classical Littlewood–Richardson/Pieri/Jacobi–Trudi/Young rules, and an
exact finite calculation in the stated degrees. I re-derived both branches by
hand and recomputed the finite bases with independently written code that uses
different algorithms. The editorial points in §7 are optional. None of them changes
the frozen statement.

Hashes certify byte identities only. They do not certify mathematics, source
truth or novelty.

## 1. What was reviewed and its identity

Author packet `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r38/`.
Before parsing the inventory, I compared `manifest.json` with the dispatched
anchor `29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9`
and found a match. All other dispatched anchors also matched: verify.py `5b27e887…`,
candidate205m.md `17b2b35c…`, scope205m.md `3eb9d790…`, source-and-credit.md
`fe5d374d…`, kostka-low-capacity-proof.md `d8e029e9…`,
provenance/parent-high-capacity.md `fc155c9a…`, finite-proof-certificate.json
`5ffb1880…`. The full hashes are in `identity-check-out.json`.

- I read the author `verify.py` before running it. It is read-only. On a `/var/tmp` copy, the
  author `verify.py` passed with the correct anchor (78 files, 13 directories) and
  failed with `external manifest anchor mismatch` on the all-zero anchor.
  The same read-only verifier also passed on the canonical packet. Nothing was written there.
- My own `identity-check.py` hashed the separately anchored canonical
  `sources/preprints-tree.json` (SHA256 `eeecc1da…dc5e09b`, 13223 entries,
  `truncated:false`). It did not use the author's private copy, although that copy is
  byte-identical. The script checked all 21 selected source copies by Git blob id against
  that canonical tree, and it rebuilt the selection from the complete 42-entry
  family listing. The 14 unselected family blobs are PDFs, verification code
  and logs. None of them is a proof input.
- I searched all 749 top-level preprint directories in the canonical tree by title
  (Saxl, tensor, Kronecker, staircase, Specht, Kostka, partition,
  representation, character, …). No other family is a symmetric-group
  tensor-square source. This was a title search only.
- I read `control-tests.py` before running it. It was run **only** on the
  `/var/tmp/t205m-proof-r1-work/packet` copy. Result: `PASS_13_INVENTORY_CONTROLS`, with all 11 mutations
  rejected for the expected reasons. The output is in `author-control-tests-out.json`.
  I did not modify, reseal or write any file in the canonical author packet.

## 2. Source interfaces (exact statements read)

1. `dominance.tex`, full. `thm:cyclic-saxl` says that every S^λ occurs in
   W_m = C[G_m](v_R⊗v_C). The proof of `prop:dominated` gives a submodule Z_m of an
   isomorphic image of W_m⊗ε, with Q(Z_m) = M^{ρ_m}. Multiplicity upgrade: by
   semisimplicity, [W_m⊗ε:S^τ] ≥ [Z_m:S^τ] ≥ [M^ρ:S^τ] = K_{τ,ρ}. Twisting
   by ε then gives (4), [W_m:S^λ] ≥ K_{λᵗ,ρ_m}, with multiplicities. I21's
   injectivity remark is not needed.
2. `band-quotient.tex`, full. `prop:band-quotient` (s∈{1,2}, h=m−s≥1) gives
   a G-equivariant **surjection** of W_m onto the whole of
   Ind_{S_D×S_F}(W_h⊠U_{m,s}). Here W_h is the specified smaller cyclic
   module, transported to the high letters. The sector lemma gives an isomorphism
   C[G]z ≅ Ind_H^G A_0, and A_0 = W̃_h⊠U_{m,s} exactly. So
   [W_m:S^λ] ≥ Σ_{ν,η}[W_h:S^ν][U:S^η]c^λ_{ν,η}. This is the full induced
   multiplicity, not support only, and W_h is never replaced by its ambient square.
3. `path-band.tex`. Read: lines 1–30, 126–181, 231–254 and 285–321. Not read:
   31–125, 182–230 and 256–284. Line 14 gives U_{m,1} ≅ S^{(m)}. Lines 245–248
   (`prop:two-band`, m≥3) say that every S^η with η⊢2m−1 and len(η)≤4 occurs in
   U_{m,2}. Only this support statement is used: one copy of each such η is enough
   for the lower bound. The candidate's multiplicity-free identification of U_{m,2}
   (Bessenrodt–Bowman) is not load-bearing. I did not read or certify it.
4. Kirillov, arXiv:hep-th/9304099v2 (private text). Read lines 1–~40 and
   60–344. Not read: lines ~40–59 and 345–497, which cover the rest of the
   sufficiency proof of Theorem 2.1, Theorem 2.2 and the references. Used:
   Theorem 1.1, which writes K_{λμ} as a sum over admissible configurations of
   ∏ binom(P+Q,Q) with P_n^{(k)} = Q_n(ν^{(k−1)}) − 2Q_n(ν^{(k)}) + Q_n(ν^{(k+1)}) and ν^{(0)}=μ;
   Corollary 1.3 (the maximal configuration); and the perturbation identity (2.3)/(2.4).
   See editorial note E1 on the matrix-size wording.

## 3. Recursion and invariant (scrutiny items 1–2, 7)

(5) takes the **maximum** of four separately valid lower bounds for
[W_m:S^λ]. Those bounds are cyclic support, the dominance quotient, the s=1
quotient and the s=2 quotient. Within one induced quotient, distinct
(ν,η) LR terms are **added**, which semisimplicity of the induced module allows.
Induction on m gives R_m ≤ [W_m:·], starting from R_1((1)) = 1 = [W_1:S^{(1)}].
The invariant (7) is stated for R_h, not for the ambient square or its
transpose maximum. The sign symmetry S^ρ⊗S^ρ ≅ (S^ρ⊗S^ρ)⊗ε is used only
at the end, in (6). The critical family gets its two contributions from one
two-band quotient: ν = (2,1^{n−2}) with η ∈ {(m,m−3,1,1), (m−1,m−2,1,1)}.

Final assembly: (7) holds for h=5,6 by the exact recursion, at m=7,8 by the
finite steps, and for m≥9 by §§4–6. For m≥5, a label λ outside E_m is covered by
(7). For H_m and J_m, the transposes have first rows N−m+1 and N−m, both greater than m,
and are not rows. So they lie outside E_m. The cases m=2,3,4 are handled by the
exact squares, with minima 1,2,3. Sharpness:
⟨χ^ρχ^ρ, π−1⟩ = ⟨Res χ^ρ, Res χ^ρ⟩ − 1 = m − 1, where π is the natural
permutation character. The staircase has m removable corners and branching is
multiplicity-free. Every quantifier of the frozen statement is covered.

## 4. Wide branch, λ_1 > m (item 3), re-derived

- Horizontal m-strips are counted by [x^m]∏(1+⋯+x^{g_i}) with Σg_i = λ_1.
  For two nonconstant factors, the coefficient at k is min(k,a,b,a+b−k)+1 ≥ 2
  for 0<k<a+b. Multiplying by further factors with all coefficients ≥1 keeps every
  interior coefficient ≥2, because a split k = i+j with 0<i<d exists.
- Exception exclusion, with h=m−1≥8: (i) If the row is a predecessor, λ has at most two rows, and the
  other predecessor is a two-row non-row, so it is not exceptional. (ii) If the column is a predecessor, λ is the hook
  (m+1,1^b), and its other predecessor (2,1^{b−1}) has width 2, so it is not exceptional. (iii) If both
  H_h and J_h are predecessors, ν' = (h+1,1^{N_h−h−1}) interlaces. This needs h+1 ≤ λ_1,
  λ_2 ≤ h, λ_3 ≤ 1 ≤ λ_2, and length N_h−h = len(J_h). It is a nonexceptional hook of width h+1.
  The bound is therefore (m−2)+1.
- Rectangle (a^b), a≥m+1, b≥2: the complements ν_i =
  (a^{b−2}, a−η_{i,2}, a−η_{i,1}) give c=1. Both have size N_{m−2}. Both are
  nonexceptional: if b≥3, the first row a>h and there are at least two rows; if b=2, there are at most two rows,
  ν_2 has two rows because a≥m+1, and ν_1 is a single row only if a=m+1 and 2(m+1)=N_m, which forces m=4. The bound is 2(m−3) ≥ m−1.

## 5. High-capacity branch (item 4), re-derived line by line

- For μ = (λ_5,…), partitions μ⊆ν⊆λ correspond exactly to order ideals of S=λ/μ.
  Here k = C−(2m−1) ∈ [2, C−2].
- Unique-rank cut: if A is the unique rank-r ideal, then an incomparable pair a∈A, b∉A gives an
  acyclic extension and a second ideal. So all pairs satisfy a<b. Then the column cuts give:
  c<d, or 1<c=d<w, forces H_1 ≤ L_w, hence H_w = H_1 = 1 and C ≤ m. c=d=1 forces r≤1.
  c=d=w forces |B|≤1. w=1 is excluded because C≤4. I checked each case.
- If any exception fits, then λ_7 ≤ 1 and len(λ) ≥ (m−2)(m−3)/2 ≥ 10. So the four
  first-column cells of S (rows ≥7) are incomparable with the rest, which lies in rows ≤6
  and columns ≥2. That gives at least min(4,k)+1 ideals. The exceptional lengths n, n−h+1, n−h
  allow at most two exceptions at once, since a predecessor's length window is 4 < h.
- k=2: a predecessor's length lies in H_1−4+{0,1,2}, so S_h cannot coexist with H_h or J_h.
  If H_h and J_h both fit, the off-first-column count gives
  λ_5 ≥ h−1. Then C ≥ 4(m−3) > 2m+1 for m ≥ 7.
- Four-strip to LR: filling each skew column with 1,2,3,4 from the top gives an SSYT,
  since the entry in row i, column j is i−ν'_j and ν'_j is weakly decreasing.
  So s_{λ/ν}(1⁴) > 0, and some η with len ≤ 4 has c^λ_{ν,η} > 0. Two distinct ν give at least 2(m−3).

## 6. Low-capacity branch (item 5), re-derived

Conventions check (α = Lᵗ, μ = ρ): Q_n(ρ)−Q_n(α) = Σ_{j≤n}(ρ_j−L_j) = D_n.
The maximal first vacancy is D_n + min(n,α_1) − min(n,α_2), which equals D_n for n ≤ t = α_2.
For k≥2, every occupied length has vacancy 0. So M is the product (2.2). If s=0, the
j=t multiplicity is L_t−1 rather than L_t, but then D_t = 0 and the factor is 1.
Moving one conjugate cell from column v to column u changes only ν^{(1)}. It lowers P^{(1)} by 2 and raises
P^{(2)} by 1, exactly on [u,v) ⊆ [1,t).

I checked each case:
(2.1) average argument, D_j ≥ j(d−j+1)/2 ≥ d−1 on [4,d−1];
dominance for w≤d−2 and for w=d−1 (at least four rows because N/(d−1) > 4);
the u=1, v=t partition condition; the j=1 factor ≥ d−w−1 (Q̃_1 = w−L_2+1);
the j=t−1 factor ≥ D_{t−1}−1 (Q̃ = L_{t−1}−L_t+1);
the second-level product ≥ w−v_0+1, using zero old vacancy at occupied lengths and the
telescoping sum; D_{t−1} = v_0+s for t ≥ d+1; (v_0−1)(w−v_0+1) ≥ w−1;
the widths 3..d−2 cases with t=1,2,3,4,≥5, including the w=d−2 split M ≥ 3 and M+W ≥ d
(distinct configurations add);
width two: D_t ≥ d−1, D_d = s = d(d−3)/2, t−2 ≥ d. For ν^{(1)} = (t−2,2), the vacancies
are d−4, 2d−9, concave on [2,t−2] down to the endpoint s, and s beyond. The weight is (2d−8)(s+1) ≥ d;
width d−1: M = (d−v)binom(d−1,v−1); L_3 ≤ a and v ≤ d−2; a < d/2 gives
M ≥ a(d−a); a ≥ d/2 gives the u=2 perturbation with factors a−1 (Q̃_1 = a−2,
P=1) and ≥ a−1 (P̃_2 = a−2), so W ≥ (a−1)² ≥ d for d ≥ 8.
Exceptions: exact K values are d−1 for (2,1^{N−2}), (d−1,1^{…}) and
(d−1,d−1,1^{…}), and 1 for the column.

Application: the full-column deletion (9) is a bijection, because the first column of λᵗ is forced
to be 1..m. Then L_1+L_2+L_3 ≤ m = h+1 and the top four sum to at most 4(h+1)/3 ≤ 2h.
L_1 ≤ h−1 (see E2). The column and width-two hook give H_m and J_m. The double exception
is impossible. The width-(h−1) hook gives (10). For (10), λ/ν = D ⊔ (1⁴).
I checked s_D = h_{m−2}h_{m−3} − h_m h_{m−5} = s_{(m−1,m−4)} + s_{(m−2,m−3)} by
Jacobi–Trudi and Pieri, and multiplication by e_4 gives the two distinct four-row η.
The proof uses the lemma at d=m and d=m−1, both ≥ 8 for m ≥ 9.

## 6a. Finite bases (item 6)

I read all the author code before running it: `verify-finite-proof.py`,
`quotient-diagnostic.py`, `exception-induction-diagnostic.py`,
`multiplicity-diagnostic.py` and `finite-crosscheck.py`. Partition enumeration is
exhaustive. MN uses beta sets, with the sign given by the number of beads crossed. z_μ is correct.
Induction (12) is the standard class formula. Kostka is computed by removing
horizontal strips. rem4 enumerates exactly λ_i ≥ ν_i ≥ λ_{i+4}. The integer and Fraction arithmetic is
exact. Replay on the copy: PASS_FINITE_BASES, with the certificate hash reproduced.
Crosscheck: PASS (degrees ≤ 10).

Independent recomputation (`independent.py`; it imports nothing from the packet):

- Characters are built from permutation-module characters (counting cycle placements)
  with triangular Kostka inversion. Orthogonality and dimension are checked.
- LR sums are counted as lattice-word tableaux with entries ≤ 4. They were cross-checked against
  character induction in 3079 triples.
- Strip predecessors are found by containment plus conjugate column gaps.

Results:

- The m=2,3,4 square minima are 1,2,3, attained at (N−1,1) and its sign twist.
- Exact R_h from R_1 via (5): (7) holds at h=5 (172 labels, minimum 4)
  and h=6 (788 labels, minimum 5).
- m=7: one 2349, K 1120, exact two-band LR 245. m=8: 12161 / 4948 / 864.
  These counts equal the author's, with four-strip plus critical folded into the exact two-band
  count. The critical family's exact weighted two-band sum is 11 at m=7 and 13 at m=8.
  This independently confirms the symbolic LR fallback in those degrees.

Diagnostics of the uniform lemmas (`diagnostics.py`; finite, not proofs):

- I implemented Kirillov's fermionic sum with vacancies at all n and row lengths
  unbounded. It equals the Kostka numbers for all shape/content pairs with n ≤ 7.
- The low-capacity lemma is exact at d=8,9,10. Each configuration the proof names is
  admissible and meets its stated bound.
- The high-capacity lemma holds at m=7..10, with at least 3 good predecessors.
- Full case replay of the uniform step at m=9: wide 63801, rectangle 1,
  high 21363, critical 1, low-Kostka 3964. Together with E_9 this accounts for all 89134 labels.

## 7. Objections

Required objections: **none.**

Optional editorial points (none affects any quantifier):

- **E1.** Kirillov's text says m ∈ M_{l(λ)×l(μ')}(Z). Read literally, this would bound the
  row lengths of ν^{(k)} by μ_1. Under that reading his own Corollary 1.3
  fails whenever λ_2 > μ_1, so the bound must be a misprint. The proof needs the standard
  unbounded convention, because t can exceed d and ν^{(1)} = (t−2,2) has a row longer than d.
  The manuscript should state this convention and cite a statement that uses it
  (e.g. Kirillov–Reshetikhin 1986, or Kirillov–Schilling–Shimozono). My n ≤ 7 check
  supports the convention, but it is not a proof of it.
- **E2.** Candidate §6 / lemma §6: "L_1 ≤ h" is stated without the one-line
  exclusion of L_1 = h+1. If L_1 = h+1, then L_2 = L_3 = 0, so |L| = h+1 < N_h.
- **E3.** "First vacancy equals D_j precisely for j ≤ t": it also equals D_j for j > t when
  s = 0. Formula (2.2) at j = t, s = 0 is harmless because D_t = 0 (see §6).
- **E4.** The finite verifier asserts the m=7,8 critical-family fallback from the
  uniform prose (m ≥ 5) without computing it. This is acceptable, and it is now independently computed.
- **E5.** Item 3 of candidate §2 still describes the full U_{m,2} identification. A manuscript
  should present support as the only input and the identification as optional context.
- **E6.** Chronology: scope205m.md says "13/20" and the candidate says "14/20". This is a status
  label, not mathematics.

## 8. Limits

- I read in full: candidate205m.md, scope205m.md, kostka-low-capacity-proof.md,
  provenance/parent-high-capacity.md, README.md, verify.py, control-tests.py and
  the five finite scripts named above. source-and-credit.md and reading-limits.md
  were read with some middle lines elided by the display (about 30 and 16 lines). Neither is a
  proof input. Sources: as in §2.
- Not read: BB/BBS/Vallejo bodies, I21/I17/R026 records, the companion paper,
  completion.tex, specht-tools.tex, introduction.tex, the exploratory and checkpoint files,
  formal-interfaces.md, other diagnostic scripts, the t205m-parent* directories, and the
  parallel reviewer's directory.
- Pinned source truths are stipulated and not audited. Kirillov's Theorem 1.1 is
  taken as a published primary result. Finite diagnostics are not proofs of
  universal statements. No formalization is claimed. No novelty or substantiality judgement is made.

## 9. Files and seal

`independent.py` with `independent-out.json` (finite bases);
`diagnostics.py` with `diagnostics-out.json` (finite probes);
`identity-check.py` with `identity-check-out.json` (anchors and canonical blobs);
`author-control-tests-out.json` (the author's controls, run on the /var/tmp copy);
`verify.py` (requires the externally reported manifest SHA256); `controls.py`
(copied mutation controls, to be run only on a /var/tmp copy). `manifest.json` covers every
other file. Its SHA256 is reported outside this directory.
