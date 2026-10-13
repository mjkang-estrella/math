# I238 — quantitative stability in the complete Crouzeix inequality

**Verdict: completed restricted quantitative theorem; no tenth substantial finding nominated.** There is an explicit, dimension-independent square-root disk-stability theorem for scalar quadratic witnesses with a normalized bound on an inverse polynomial. The genuinely complete problem remains unpaid. A degree-one matrix-valued equality example refutes the scalar output-rigidity step that would otherwise appear to bridge the two.

Only the five assigned I238 files were written. No agents, live sibling reads, shared ledgers, staging, commits, publication, research code, tests, numerical experiments, parameter scans, snapshots, or seals were used. Pinned results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were accepted as true, with no truth audit. Provenance and read extents are in [input-authentication.json](../experiments/i238_crouzeix_stability/input-authentication.json) and [reading-and-failures.md](../experiments/i238_crouzeix_stability/reading-and-failures.md).

## 1. Actual source interface

Family 325 contains two relevant companions, both read at the theorem and lower-operation level:

- **Direct proof**, `build/main.tex`: `thm:main` gives ||P[A]||≤2 max_{W(A)}||P|| for all finite base sizes, coefficient sizes and degrees. `lem:faber`, `prop:coefficients`, `lem:resolvent`, and the proof of `thm:domain` give the exterior coefficient contraction, the positive original-matrix resolvent, the two ordered product tests, and the sharp positive-block comparison. `lem:approx` supplies the nonempty-interior-free limit.
- **Structural proof**, `build/main.tex`: `thm:structural`, `thm:representation`, `prop:density`, `prop:extremal`, `input:analytic`, `prop:projection`, and `lem:comparison` supply the attained metric with condition number ≤2, one common normalized positive boundary density, its endpoint data, and the full two-density comparison. `cor:hilbert` extends the complete bound to all bounded Hilbert-space operators.

Their exact pinned URLs, Git blobs and SHA-256 values are in the authentication file, and primary TeX is in [literature.md](../sources/i238_crouzeix_stability/literature.md). Neither companion states the geometric deficit theorem sought here. But keeping residual terms in its proof is not yet an inverse estimate for numerical-range shape.

A direct calculation from the source retains its full deficit: if a²=Σ||Y*b_k(A)X||_HS², R=3||Y*X||_HS²+Σ_{k≥1}||X*b_k(A)Y||_HS², and E_X,E_Y,E_B are its two diagonal and positive-block slacks, then

E_X+E_Y+E_B+2R=2(4/γ²−1)a²,   E_X,E_Y,E_B,R≥0.

Here γ is the normalized matrix-valued evaluation norm on an analytic convex enclosing domain. This gives R/a²≤4ε for γ≥2−ε, ε≤1, in all coefficient sizes. The exact definitions and proof are at the end of analytic-attempt.md. A dimension-uniform inverse estimate turning this whole certificate into numerical-range shape is missing; the identity alone is technical bookkeeping, not a geometric stability result.


## 2. Complete statement of the paid restricted theorem

Let Dbar={z∈C:|z|≤1}, N=[[0,0],[2,0]], n≥2, and A∈M_n(C). Let p be a **scalar** polynomial of degree at most two satisfying

max_{z∈W(A)}|p(z)|=1.

Put T=p(A). Suppose a scalar polynomial q(w)=a+cw+sum_{j=2}^r q_jw^j, with c≠0, reconstructs A exactly:

A=q(T).

Set

L=sum_{j=1}^r j|q_j|2^{j-1},   K=L/|c|≥1,   ε=2−||T||.

**Theorem Q.** If 0≤ε≤(304K²)^(-2), there are a unitary U and an (n−2)-dimensional operator D_A such that

||U*((A-aI)/c)U−(N⊕D_A)||≤8K√ε,   ||D_A||≤2K,

d_H((W(A)−a)/c,Dbar)≤5600K⁴√ε,

max_{|z|≤1}|p(a+cz)−z|≤1200K²√ε.

The complement is omitted for n=2. Constants are independent of n and of the inverse degree r except through K. They are not optimized. Scalar degree zero or a normal/segment-range matrix cannot meet this small-deficit regime.

## 3. Proof and the precise external input

The only non-elementary stability input is **Åhag–Czyż–Virtanen, arXiv:2608.27346v3, Corollary 9.9**, whose statement and full proof through Theorem 9.8 were read. It yields, in unitary coordinates,

T_0=N⊕D,   ||D||≤2,   ||T−T_0||≤d:=8√ε.

The pinned complete bound, at scalar coefficient size, ensures ε≥0. The external corollary applies because our threshold is smaller than its `2−√15/2` threshold. This external result is not attributed to the pinned manuscripts.

Put A_0=q(T_0), c_0=|c|, e=Ld, t=Kd. Telescoping powers gives ||A−A_0||≤e, and ||A−aI||,||A_0−aI||≤2L. The two-dimensional block of A_0 is aI+cN. Consequently the compression B of A to this summand is within e of aI+cN. Comparing support functions gives the **inner** inclusion

a+(c_0−e)Dbar⊂W(B)⊂W(A).

The threshold gives t≤1/38, so c_0−e≥c_0/2. Expand p(a+z)=b_0+b_1z+b_2z². Cauchy's coefficient estimates on this inner disk give |b_1|≤2/c_0 and |b_2|≤4/c_0². Thus

||p(A)−p(A_0)||≤e(2/c_0+16L/c_0²).

Compress again, using p(aI+cN)=b_0I+b_1cN and ||T−T_0||≤d. With h=19K²d≤1/2,

|b_0|≤h,   |b_1c−1|≤h/2.

Write α=b_1c and γ=b_2c². On |z|=1−t, boundedness of p gives |b_0+αz+γz²|≤1. Exact phase alignment of the two nonconstant terms implies

|α|(1−t)+|γ|(1−t)²≤1+h,

hence |γ|≤6h+4t≤118K²d. It follows that

max_{|z|≤1}|p(a+cz)−z|≤147K²d≤1200K²√ε.

For ζ∈(W(A)−a)/c, one has |ζ|≤2K, whence

|α||ζ|≤1+|b_0|+|γ||ζ|²≤1+491K⁴d.

Dividing by |α|≥1−h/2 gives |ζ|≤1+668K⁴d. Combined with the inner disk, this gives the stated Hausdorff estimate, with 700K⁴d=5600K⁴√ε as a convenient upper bound. The telescoping estimate already proves the operator-block conclusion. This completes the proof.

All details and checks are in [analytic-attempt.md](../experiments/i238_crouzeix_stability/analytic-attempt.md). In particular the inner inclusion uses comparison of convex support functions; mere Hausdorff closeness to a disk would not on its own justify Cauchy estimates inside the numerical range.

## 4. Invariances, degeneracies, and limits

Under A↦(A−bI)/s, s≠0, transform p(z)↦p(b+sz) and q(w)↦(q(w)−b)/s. Then T and ε are unchanged, L and |c| scale by the same factor, and K and the normalized numerical range are unchanged. Unitary conjugation preserves the whole statement. A unimodular change in p is absorbed into q. Thus the normalization is intrinsic to the supplied reconstruction and respects the requested affine and unitary invariances.

Repeated eigenvalues are allowed; no eigenbasis is used. Existence of some q is exactly the usual generated-algebra condition: p is injective on distinct eigenvalues and p'(λ)≠0 on each nontrivial Jordan block (external Lemma 11.6). Existence is weaker than our bound K on a chosen q. The theorem explicitly pays that distinction.

For fixed K≤K_0, distance at least η from the specified normalized disk forces

ε≥min{(304K_0²)^(-2),(η/(5600K_0⁴))²}.

This is a uniform bound for a specified **witness/reconstruction class**, not an improvement of the complete constant for every polynomial on an intrinsic class of matrices.

The scalar degree restriction matters: the exact alignment of two powers is used. The inverse polynomial can have any finite degree but its weighted coefficient norm is charged. The arbitrary coefficient-size extension is false at the intermediate step described next.

## 5. Exact obstruction to the naive complete bridge

Take A=[[0,2],[0,0]] and P(z)=[[0,z],[1,0]]. Then W(A)=Dbar and max_{W(A)}||P(z)||=1. In coefficient-first coordinates,

P[A]=[[0,A],[I,0]],   ||P[A]||=2.

In a reordered orthonormal basis this is the forward weighted chain with weights (1,2,1). Its unique maximal right singular vector x has ||P[A]²x||=2. Hence P[A] has no reducing norm-two 2×2 nilpotent block: such a block would contain that singular vector and annihilate its second iterate. Equivalently,

sum_{k≥0}4^(−k)||P[A]^k x||²=1+1+1/4=9/4>2.

Thus the scalar square-function/near-nilpotent conclusion cannot be amplified. The example is an exact algebraic computation, not a numerical experiment. It leaves base numerical-range geometry unchanged and therefore does **not** refute complete disk rigidity itself.

There is also a genuine conditioning issue in the scalar pivot. For the 3×3 Crabb matrix C_2, p_δ(z)=(z²+δz)/(1+δ) has inverse q_δ(w)=(1+δ)w/δ−(1+δ)²w²/δ³ on the generated algebra. Yet K=1+4(1+δ)/δ² diverges as δ↓0 while p_δ→z². Dropping all inverse conditioning would destroy the affine-symbol conclusion. No parameter values were scanned.

## 6. Exact missing lemma for the desired complete result

**Q4(r), unpaid.** Fix 0<r<1. Seek constants C_r<∞ and ε_r>0 such that for every A∈M_4(C), every finite coefficient size m, and every M_m-valued polynomial P of degree at most two:

- the minimum enclosing disk of W(A) is Dbar and rDbar⊂W(A);
- max_{W(A)}||P||=1 and ||P[A]||≥2−ε, with 0≤ε≤ε_r;

imply

d_H(W(A),Dbar)≤C_r ε^(1/4).

The exponent 1/4 is a precise target, **not a proved result**. Even its zero-deficit case would require complete disk rigidity in base dimension four; neither pinned manuscript states that implication. The inspected external scalar rigidity theorem and the complete equality theorem through dimension three do not supply it.

For this target, arbitrary coefficient size reduces to at most eight by compressing coefficients to the union of the left and right singular vectors' coefficient Schmidt supports. The selected singular pairing and the evaluation norm are retained; the boundary norm decreases, so normalization can only improve the ratio. This finite reduction does not prove the zero-deficit classification or its modulus.

## 7. Prior art and substantiality

- BCD's primary Section 5.2 already proves the complete two-by-two elliptic similarity, including repeated eigenvalues. Li's primary Section 2.1 already gives the elliptic extremizer and uniqueness. A two-by-two eccentricity bound extracted from those formulas is not nominated.
- Åhag–Czyż–Virtanen already give scalar 8√ε output rigidity, scalar polynomial equality, the inverse-algebra criterion and its exact geometric consequence, and complete equality through base dimension three. Theorem Q contributes a quantitative bounded-inverse transport and explicit geometry/symbol constants. It does not claim those existing operations as new.
- Jin's primary Section 9 already gives qualitative fixed-dimension scalar disk stability through compactness. It explicitly leaves the modulus nonconstructive. Theorem Q has an exponent and base-dimension-independent constants, but only under stronger reconstruction hypotheses and for scalar quadratic witnesses.
- I39 and I130 were screened only in their short opening portions and by a targeted keyword lookup. No matching Crouzeix work was found there. This is a bounded duplication check, not an assertion that the entire project history was read.

**Honest novelty status:** Theorem Q is new to this working record. Its quantitative statement was not found in the inspected primary portions, but a literature-wide novelty claim is not established. Its key input is an existing scalar stability theorem; the remaining steps are a natural quantitative continuation of the existing inverse-algebra proof. The hypothesis is also witness-dependent, not a new intrinsic class-wide complete spectral estimate. These limits are material at the user's substantiality standard.

**Final disposition:** retain the proved restricted theorem and the amplification counterexample; leave Q4(r) open; do not nominate a tenth substantial finding and do not change the supplied count of nine.
