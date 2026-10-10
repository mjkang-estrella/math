# Review r1: proposals/number_theory.md §2 (binary Elliott/Chowla on polynomial power-free sets)

Reviewer: independent adversarial referee, first round. Date: 2026-10-08.
Pinned revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. As instructed, upstream theorems are assumed true. Only the downstream deduction is audited. I read only §2 (plus the shared "Sources and exact contracts" block that §2 cites).

**Verdict: ACCEPT WITH MINOR CORRECTIONS.** The deduction is correct. I found no logical or arithmetic obstruction and no upstream duplicate. Novelty is low. This is a formal corollary, and the write-up should present it as one (see §6).

## 1. Upstream statements checked against the cached TeX

**Family 007** (`sources/cache/number_theory/007__…__introduction.tex`, `…__affine-corollaries.tex`):

- `eq:distance` defines D(f,χn^{it};X)² = Σ_{p≤X}(1−Re(f(p)\overline{χ(p)p^{it}}))/p. `eq:unp` requires inf_{|t|≤N} D(f,χn^{it};N) → ∞ for every fixed χ, with the same N used as prime cutoff and height bound. The proposal's displayed hypothesis uses the squared distance with the same X in both places. That is equivalent. ✔
- `cor:affine` requires f_1,f_2:ℕ→𝔻 multiplicative (not necessarily completely multiplicative), at least one satisfying `eq:unp`, fixed integers a_j≥1, b_j≥0, and a_1b_2−a_2b_1≠0. It gives (1/N)Σ_{n≤N} f_1(a_1n+b_1)f_2(a_2n+b_2) → 0 for integer N. The proposal states exactly these hypotheses. ✔
- The text after `cor:affine` (and `prop:affine-progression`) says the hypothesis is on an *original* factor, and that the local changes for dilations and residues preserve it. This supports the proposal's remark that E applies "to the same original functions". ✔
- `thm:q-affine` (the Liouville log-saving) has constants depending on the forms, "no uniformity for coefficients growing with X". This matches the proposal's no-rate remark. ✔
- Liouville satisfies `eq:unp` (stated in the intro, proved in `lem:affine-liouville-unp`). ✔

**Family 020** (`020__…__01-introduction.tex`, `cor:separable-products`): fixed k≥2, and fixed nonzero F_i∈ℤ[x], each separable over ℚ with all nonconstant irreducible factors of degree ≤k+2. Shared factors are allowed. Ω_p = {a∈ℤ/p^kℤ : p^k | F_i(a) for at least one i}. If #Ω_p<p^k for all p, then S_{𝐅,k}(N), which counts 1≤n≤N with every F_i(n) k-power-free, equals c N+o(N) with c=∏_p(1−#Ω_p/p^k)>0. The proposal's "S" contract (union of root sets mod p^k, not the product) matches exactly. ✔

I also grepped all cached 007 files for squarefree/power-free conditioning of correlations, and all 020 files for Liouville/Chowla/Elliott. Neither family states the combination. **No upstream duplicate.**

## 2. Periodic approximation (eq. 6) and the double limit

- w_Y(n)=1 iff n mod p^k∉Ω_p for all p≤Y. This is periodic mod Q_Y=∏_{p≤Y}p^k. By CRT its mean is exactly c_Y=∏_{p≤Y}(1−#Ω_p/p^k). ✔
- w≤w_Y pointwise, because a k-power-free value has no p^k divisor. So |w_Y−w|=w_Y−w, and its mean tends to c_Y−c: the periodic mean is exact and the mean of w comes from S. c_Y decreases to c by the definition of the convergent product, and c>0 by S. ✔
- Order of limits: Y is fixed while N→∞, which gives limsup ≤ c_Y−c. Then Y→∞. This is legitimate because the left side does not depend on Y. ✔

**Correction (minor):** "Ignore finitely many integer zeros" is ambiguous. Define w exactly as S does: n counts only if every F_i(n) is k-power-free, and 0 is not k-power-free since every p^k divides it. Then w≤w_Y holds at every n, not just away from finitely many exceptions. Either reading changes only O(1) terms, so this is cosmetic.

## 3. Residue split, affine transform, determinant

Write n=Q m+a with Q=Q_Y, a∈{1,…,Q}, m≥0. Then L_j(n)=(a_jQ)m+(a_ja+b_j).
- Slopes a_jQ≥1, and intercepts a_ja+b_j≥0 (in fact ≥1). ✔
- Determinant: (a_1Q)(a_2a+b_2)−(a_2Q)(a_1a+b_1)=Q(a_1b_2−a_2b_1)≠0. ✔
- Only finitely many residues a are summed, and Q is fixed while N→∞. ✔
- The m=0 term (n=a) is not covered by cor:affine's range n≥1. It costs ≤1 per residue, ≤Q_Y in total, which is O(1) for fixed Y. ✔
- **Correction (minor, expository):** say explicitly that cor:affine is applied at the integer cutoff M_a=⌊(N−a)/Q⌋ and that M_a/N→1/Q, so o(M_a)=o(N). The proof currently leaves this implicit.
- No coprimality between the polynomials and the forms is needed, because cor:affine allows nonunit intercepts and common factors, and w_Y is simply a union of residue classes. Example: F=x, k=2, L=(n,n+1) gives squarefree n with prescribed (μ(n),μ(n+1)) sign pattern at density (6/π²)/4. This agrees with 007's Möbius specialization. ✔

## 4. One-factor inference and the c/4 sign proportions

- One-point terms: take f_2≡1, which is multiplicative with values in 𝔻, f_1=λ satisfying `eq:unp`, and any auxiliary form nonproportional to L_1 (for example (a_1, b_1+1)). Then cor:affine gives Σ w λ(L_1(n))=o(N) through the same approximation argument. ✔ (Classical PNT in progressions would also work. Either is fine.)
- Expanding ¼(1+ε_1λ(L_1))(1+ε_2λ(L_2)) gives a constant term with mean c/4. The two one-point terms and the ε_1ε_2λλ term are o(N). This gives (5). ✔

## 5. The n⁴+1 example

- Hypotheses of S: k=2, and t⁴+1=Φ_8 is irreducible of degree 4≤k+2=4 and separable. ✔
- p=2: t⁴+1≡1 or 2 (mod 4), so there are no roots mod 4 and the factor is 1. ✔
- Odd p: disc(t⁴+1)=256, so roots are simple. t⁴≡−1 means t has order 8 in 𝔽_p^×. That happens iff p≡1 (mod 8), and then there are exactly 4 roots. Otherwise there are 0 roots, even though the polynomial factors into quadratics. Hensel lifting gives ρ(p²)=ρ(p). #Ω_p=4<p² holds trivially. ✔
- The forms n and n+1 have determinant 1. ✔
- Constant: c=∏_{p≡1(8)}(1−4/p²)≈0.98082, so c/4≈0.24520.
- Numerical sanity check (not a proof): N=10⁶ in pure Python, with λ computed by a smallest-prime-factor sieve and squarefreeness tested at primes p≡1 (8), p≤10⁶, using roots Hensel-lifted mod p². The four sign-pair proportions were 0.24469, 0.24557, 0.24544, 0.24514, against the predicted 0.24520. These are consistent. Script was a transient /tmp file; it is easy to reproduce from this description.

## 6. Uniformity, synthesis, and novelty

- **No rate:** this is correct and honestly stated. S provides only o(N). 007's general theorem has no rate, and its Liouville rate has form-dependent, possibly ineffective constants with no uniformity in coefficients like Q_Y. Rewording suggestion: "Even for Liouville the conclusion is o(N)" should read "only o(N) is proved". Nothing here shows that no rate is possible.
- **Cross-family obstruction search:** none exists, and none can. 007 gives cancellation in every fixed residue class, nonunit ones included. The only joint structure w imposes is local (residue classes mod p^k). Λ-type signs carry no periodic structure that could correlate with w_Y. Shared prime factors between F_i(n) and L_j(n) (e.g. F=x, L=n) are absorbed by the nonunit-class allowance. I tried F_i equal to a form, shared factors, and zero intercepts. None breaks the argument.
- **Novelty (recommended reframing):** the argument is the standard principle that binary Elliott in all fixed progressions transfers to any rationally almost periodic (RAP, Besicovitch-limit-of-periodic) weight. The only real input is 020's theorem that these power-free sets have the Euler-product density, which makes w RAP with explicit approximants w_Y. I recommend stating the abstract lemma once ("if w:ℕ→[0,1] is a Besicovitch limit of periodic functions, then (4) holds with weight w") and presenting the quartic/power-free family and the n⁴+1 sign law as instances. The lemma is classical and should be labelled as such. The instances are new-to-project corollaries of the assumed 007+020 theorems. The proposal's novelty section already cites Desjardins and avoids claiming a method. That is appropriate. Keep the caveat that a literature search on one-variable squarefree-value/Chowla combinations is still incomplete, so no new-to-literature claim is justified.

## 7. Required changes (all minor)

1. Define w to match S exactly (zeros contribute w=0) instead of "ignore finitely many integer zeros".
2. State the integer cutoff M_a=⌊(N−a)/Q_Y⌋ and M_a/N→1/Q_Y in the residue step.
3. Reword the uniformity remark so it says only that no rate is *proved*.
4. Optionally factor out the RAP-weight lemma and label it standard. The result's value is in the instances, and the n⁴+1 sign law is a clean showcase.

No mathematical errors found. Accept after these edits.
