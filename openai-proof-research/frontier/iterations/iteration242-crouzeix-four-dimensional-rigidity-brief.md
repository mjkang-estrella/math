# I242: complete Crouzeix geometry
Work only in /home/mj-kang/Documents/Dev/math/openai-proof-research. Read AGENTS.md and sources/upstream.json. Assume ALL pinned OpenAI theorems/lower operations true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; do not audit them. Nine accepted; one remains, with no standard lowered. GPT-6.1 Sol/high/ultrafast. No subordinate agents, live sibling reads, shared edits, staging, commits, publication, research code, tests, numerical experiments/scans, snapshots, seals or giant history replay. Retrieval, extraction, bounded source lookup and provenance hashes allowed. Write early partial mathematical notes. Read actual primary statements, companions, and primary literature. Only fully read excerpt copies retained. Return exact quantifiers, paid proof or precise gap, active counterexamples, contribution limits and detached hashes.
I238's original brief, final report, proof and reading record follow. The exact scalar theorem is technical and must not be counted. The actual complete spectral bound is stipulated; its scalar output-rigidity extension is refuted by the explicit weighted-chain example. That example does NOT refute base numerical-range disk rigidity. The literature file frontier/sources/i238_crouzeix_stability/literature.md contains complete retained primary text; consult the exact sections needed, not a blind giant dump. Do not read I241 or any other live output.

Focus on Q4(r) from I238. Use the actual direct complete proof's exact nonnegative deficit identity and positive boundary representation to prove a genuinely new complete disk-rigidity theorem in base dimension4, initially for matrix-valued degree<=2 witnesses, with inball/nondegeneracy normalization. Exact equality is a worthwhile first target; an explicit power modulus is stronger only after equality is paid. Do NOT merely import scalar nilpotent output rigidity. Find the missing inverse statement that turns vanishing backward coefficients and positive-block slacks into geometric disk structure, or produce an actual non-disk exact equality counterexample. Primaryreading and sourcecontractcheck needed. Existing qualitative compactnessmoduli and semialgebraic existence without substantive equalityclassification do not count. Two routes: trace residual geometry, and operator-valued maximum/Schur model. Write only frontier/iterations/i242-crouzeix-four-dimensional-rigidity.md, frontier/experiments/i242_crouzeix_four_dimensional_rigidity/{analytic-attempt.md,reading-and-failures.md,input-authentication.json}, frontier/sources/i242_crouzeix_four_dimensional_rigidity/literature.md plus fully read primary excerpts.

## Original I238 brief
# I238 — quantitative stability in the complete Crouzeix inequality
Work only in /home/mj-kang/Documents/Dev/math/openai-proof-research. Read AGENTS.md, sources/upstream.json, family325 catalogue and ACTUAL pinned manuscript/theorem/lower operations/companions. All pinned results are true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, no source truth audit. We have nine substantial findings; user says continue to ten without lower standards. GPT-6.1 Sol/high/ultrafast. No subordinate agents. No live sibling reads, shared ledgers, staging, commits, publication, research code, tests, numerical experiments, parameter scans, snapshots, seals or giant historical replay. Retrieval, text extraction, bounded local lookup and provenance hashes permitted. Write partial mathematics early. Read primary literature, not just snippets.
Explore a fresh spectral-operator bridge from the complete Crouzeix constant2 theorem. Seek a genuinely nontrivial quantitative stability/rigidity theorem near equality, or a dimension-uniform improvement for a precisely specified structural class not directly substituted into source. A possible start is 2x2 matrices or degree1/2 matrix-valued polynomials, but simple normal/Jordan examples and applications to functional calculus are standard and cannot count. Can a deficit control distance to extremal numerical-range geometry, with an explicit exponent and normalized nondegeneracy? Check scale/translation/unitary invariances, repeated eigenvalues, degree/matrix-size dependence, and counterexamples. If source already contains all such rigidity, switch once to another genuinely new operator-class bridge enabled by it; do not force a theorem. Need complete proof or exact missing lemma, and separate honest novelty/substantiality discussion. Read only relevant short portions of old I39/I130 discovery records to avoid exact duplication, no broad history replay.
Write only frontier/iterations/i238-crouzeix-stability.md, frontier/experiments/i238_crouzeix_stability/{analytic-attempt.md,reading-and-failures.md,input-authentication.json}, frontier/sources/i238_crouzeix_stability/literature.md and fully read primary excerpts there. Return full exact statement, proof/unpaid step, prior-art comparison, verdict, and detached hashes.

## Completed frontier/iterations/i238-crouzeix-stability.md
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


## Completed frontier/experiments/i238_crouzeix_stability/analytic-attempt.md
# I238 — analytic work in progress

## First constraint (before selecting a theorem)

For a bounded operator A, define C_cb(A)=sup_{m,P≠0} ||P[A]||/sup_{W(A)}||P||. The source supplies C_cb(A)≤2. This ratio is unchanged by unitary conjugacy and by A↦aA+bI, a≠0, after composing P with the inverse affine map. Any geometric deficit statement must therefore fix a center and a scale, and distinguish the full numerical range from an extremal reducing summand.

A disk numerical range is not itself proximity to a single 2×2 Jordan block: orthogonal direct sums of identical extremal blocks are extremal at every multiplicity. Moreover, adding any summand whose numerical range is contained in the same disk preserves both the numerical range and the scalar extremal witness p(z)=z. Thus a claim that small deficit forces a whole operator to be close to one irreducible block is false without an explicit nondegeneracy condition. This obstruction is algebraic, not a numerical experiment.

A candidate that survives this first check is a quantitative statement for a specified low-degree witness or for an approximate reducing extremal block. No positive novelty claim is made at this stage.

## A paid scalar-quadratic bridge (partial result; not a tenth finding)

Let p be a scalar polynomial of degree at most two with sup_{W(A)}|p|=1, and put T=p(A). Suppose A=q(T) for a scalar polynomial q(w)=a+cw+sum_{j≥2}q_jw^j with c≠0. Define L=sum_{j≥1}j|q_j|2^{j-1} and K=L/|c|≥1. For ε=2-||T|| in [0,(304K²)^(-2)], the proposed paid conclusion is

- d_H((W(A)-a)/c, closed unit disk) ≤5600K⁴√ε;
- sup_{|z|≤1}|p(a+cz)-z| ≤1200K²√ε;
- after a unitary change of basis, ||(A-aI)/c - (N⊕D_A)||≤8K√ε, where N=[[0,0],[2,0]].

This uses the existing scalar estimate ||T-(N⊕D)||≤8√ε of Åhag–Czyż–Virtanen, Corollary 9.9, whose proof was read. The new work is bounded inverse-polynomial transport plus inner-disk coefficient control, not that scalar estimate. A proof with all constants is being consolidated below. The coefficient dimension is one; an arbitrary matrix-valued p is not covered.

## Exact amplification obstruction

Let A=[[0,2],[0,0]], and let P(z)=[[0,z],[1,0]]. On W(A)=closed unit disk, ||P(z)||=max(1,|z|), so its supremum is one. In coefficient-first order T=P[A]=[[0,A],[I,0]] has norm two. In the chain basis (e_2⊗f_1,e_2⊗f_2,e_1⊗f_1,e_1⊗f_2), its forward weights are (1,2,1). It is irreducible and T² sends its unique maximal right singular vector to a vector of norm two. Hence T has no reducing two-dimensional nilpotent block of norm two. The scalar square-function inequality is also false: on that maximal right singular vector x, sum_{k≥0}4^{-k}||T^k x||²=1+1+1/4=9/4>2. No numerical calculation is used.

Consequently the complete constant-two theorem cannot be supplemented with the scalar output-rigidity theorem by merely replacing a scalar polynomial with a matrix polynomial. This does not disprove numerical-range rigidity for the base A, whose range here is a disk.

## Completed theorem and proof

Write Dbar={z∈C:|z|≤1} and N=[[0,0],[2,0]]. All matrix norms are operator norms; d_H is Euclidean Hausdorff distance. The first tensor factor convention of the pinned source is used when matrix polynomials occur.

**Theorem Q (bounded inverse reconstruction, scalar quadratic witnesses).** Let n≥2, A∈M_n(C), and let p be a scalar polynomial of degree at most two with max_{W(A)}|p|=1. Let T=p(A), and suppose that a scalar polynomial

q(w)=a+c w+sum_{j=2}^r q_j w^j,   c≠0,

satisfies A=q(T). Put

L=sum_{j=1}^r j|q_j|2^{j-1},   K=L/|c|≥1,   ε=2-||T||.

If 0≤ε≤(304K²)^(-2), then there are a unitary U, a two-dimensional orthogonal summand, and an operator D_A on its complement for which

(1) ||U*((A-aI)/c)U - (N⊕D_A)||≤8K√ε,   ||D_A||≤2K;

(2) d_H((W(A)-a)/c,Dbar)≤5600K⁴√ε;

(3) max_{|z|≤1}|p(a+cz)-z|≤1200K²√ε.

The complement is absent when n=2. The constants have no dependence on n or r except through K. The theorem does not assert that p can have matrix coefficients.

**Inputs.** The pinned complete inequality, restricted to m=1, gives ||T||≤2. The nontrivial scalar stability input is Åhag–Czyż–Virtanen, arXiv:2608.27346v3, Corollary 9.9 (with its Theorem 9.8 proof): for normalized scalar p and sufficiently small ε, there are U and D with ||D||≤2 such that, in these coordinates,

T_0=N⊕D,   ||T-T_0||≤d:=8√ε,   ||T_0||≤2.

Here D is a compression of T. Our ε threshold is smaller than their 2−√15/2 threshold. This input is external literature, not an additional statement attributed to the pinned manuscripts. It is precisely the scalar statement that the amplification counterexample above prevents one from using for matrix-valued P.

**Proof.** Work in these unitary coordinates. Define A_0=q(T_0), c_0=|c|, e=Ld and t=e/c_0=Kd. Telescoping X^j−Y^j=sum_{l=0}^{j-1}X^l(X−Y)Y^{j-1-l}, which does not require X,Y to commute, gives

||A-A_0||≤Ld=e.

Also ||A-aI||,||A_0-aI||≤sum_{j≥1}|q_j|2^j≤2L. Since N²=0, the two-dimensional block of A_0 is aI+cN. Dividing by c proves (1); D_A=(q(D)-aI)/c has norm at most 2K.

Let B be the compression of A to that two-dimensional summand. The norm distance between B and aI+cN is at most e, so their numerical-range support functions differ by at most e. Since W(aI+cN)=a+c_0 Dbar, for every unit complex ν,

h_{W(B)-a}(ν)≥c_0-e.

The support-function characterization of inclusion for compact convex sets therefore gives

a+(c_0-e)Dbar⊂W(B)⊂W(A).                                      (4)

This is an inner disk, not merely Hausdorff closeness to some disk. The assumed ε threshold gives d≤1/(38K²), t≤1/38, and in particular c_0-e≥c_0/2.

Expand p about a:

p(a+z)=b_0+b_1z+b_2z².

By (4), Cauchy's coefficient bounds on the disk of radius c_0-e give

|b_1|≤2/c_0,   |b_2|≤4/c_0².

Consequently

||p(A)-p(A_0)||≤e(2/c_0+16L/c_0²).

Compress to the same two-dimensional summand and use ||T-T_0||≤d. Since p(aI+cN)=b_0I+b_1cN,

||b_0I+(b_1c-1)N||≤d(1+2K+16K²)≤h:=19K²d≤1/2.

Reading a diagonal entry and the nonzero off-diagonal entry gives

|b_0|≤h,   |α-1|≤h/2,   α:=b_1c.

Set γ=b_2c². On the circle |z|=1-t, (4) gives |b_0+αz+γz²|≤1. The maximum of |αz+γz²| on that circle is exactly |α|(1-t)+|γ|(1-t)², by aligning the two phases. Therefore

|γ|≤[1+h-(1-h/2)(1-t)]/(1-t)²≤6h+4t≤118K²d.          (5)

For |z|≤1, equations (5) and the preceding bounds yield

|p(a+cz)-z|≤h+h/2+118K²d≤147K²d≤1200K²√ε,

which proves (3).

For every ζ∈(W(A)-a)/c, the bound ||A-aI||≤2L gives |ζ|≤2K. Hence

|α||ζ|≤1+|b_0|+|γ||ζ|²≤1+19K²d+472K⁴d≤1+491K⁴d.

Since |α|≥1-h/2 and h≤1/2,

|ζ|≤(1+491K⁴d)/(1-h/2)≤1+668K⁴d≤1+700K⁴d.

Together with (4), after scaling by c, this sandwiches the normalized numerical range between disks of radii 1-t and 1+700K⁴d. Their support functions show

d_H((W(A)-a)/c,Dbar)≤700K⁴d=5600K⁴√ε.

This proves (2) and the theorem. No asymptotic term or unproved estimate occurs in the deduction after the named scalar literature input. ∎

### Checks and consequences

- **Affine invariance.** For A'=(A-bI)/s, s≠0, use p'(z)=p(b+sz) and q'(w)=(q(w)-b)/s. Then T is unchanged, L and |c| are both divided by |s|, K and ε are unchanged, and (W(A')-a')/c'=(W(A)-a)/c. The prime on p' here denotes a transformed polynomial, not differentiation. Unitary conjugation also preserves everything. Multiplying p by a unimodular scalar and compensating q leaves L,K and ε unchanged, rotating the normalized geometry and its unit disk.
- **Repeated eigenvalues.** No diagonalization or simple-spectrum assumption is used. A=2J_2, p(z)=z, q(w)=w gives K=1 and equality. Existence of some polynomial inverse A=q(p(A)) is characterized by injectivity of p on the distinct eigenvalues and p'(λ)≠0 on every nontrivial Jordan block (external Lemma 11.6). The theorem additionally controls the coefficients of a chosen inverse and requires its linear coefficient to be nonzero.
- **Actual structural improvement.** On witnesses with K≤K_0 and d_H((W(A)-a)/c,Dbar)≥η>0, the deficit is at least min{(304K_0²)^(-2),(η/(5600K_0⁴))²}. This is a dimension-uniform witness-class bound. It is not a bound for the complete Crouzeix constant of every A in an intrinsic matrix class.
- **Degree.** The key phase alignment in (5) uses exactly two nonconstant powers. For higher degree, Parseval only gives a square-root estimate on the tail from these data, so the same exponent and constants are not asserted. The inverse q can have arbitrary finite degree; L pays for it explicitly.
- **Coefficient size.** The theorem has scalar p only. The degree-one 2×2 matrix-valued counterexample above rules out the intermediate scalar reducing-block input for general P, even at ε=0.
- **Loss of inverse conditioning.** At the 3×3 Crabb matrix C_2, p_δ(z)=(z²+δz)/(1+δ), δ>0, has an inverse on the generated algebra because p_δ'(0)≠0. With x=(1+δ)w, the inverse is q_δ(w)=x/δ−x²/δ³ since C_2³=0. Here c=(1+δ)/δ and K=1+4(1+δ)/δ², which diverges as δ→0. The normalized polynomials converge to z², so dropping all inverse conditioning would contradict any conclusion forcing the symbol to become affine. This is an exact symbolic family, not a parameter scan.

## Exact unpaid complete target

**Q4(r), unproved.** Fix 0<r<1. Do there exist C_r<∞ and ε_r>0 such that for every A∈M_4(C), every finite coefficient size m, and every M_m-valued polynomial P of degree at most two, the following hypotheses imply the following conclusion?

- The unique minimum enclosing disk of W(A) is Dbar, and rDbar⊂W(A).
- max_{W(A)}||P||=1 and ||P[A]||≥2−ε, 0≤ε≤ε_r.
- Conclusion: d_H(W(A),Dbar)≤C_r ε^(1/4).

The quarter-power is a target, not a proved exponent. Even its ε=0 assertion requires complete disk rigidity in base dimension four, which neither pinned proof states and which the inspected scalar rigidity paper does not prove. This is the exact missing lemma retained here. The scalar inverse-conditioned result does not pay it. The amplification counterexample attacks one attempted proof, not Q4(r).

For this polynomial target it suffices to handle coefficient size 8. Indeed, a unit left/right singular pair has coefficient Schmidt supports of dimensions at most 4 each; their union has dimension at most 8. Compress every coefficient to this union. The selected singular pairing is unchanged and the boundary norm cannot increase; embedding back shows the evaluation norm is exactly retained. Dividing by the possibly reduced boundary norm gives a normalized witness with ratio at least as large. If the original witness is exactly extremal, the pinned bound forces the compressed boundary norm to stay one. This removes unbounded coefficient size but supplies neither exact rigidity nor its quantitative modulus.


## Direct complete source residual: proved, but no geometric inverse

There is a short exact deficit decomposition in the actual direct proof. Let Ω be one of its analytic convex domains, W(A)⊂Ω, F matrix-valued with max_{∂Ω}||F||=1, and γ=||F[A]||>0. Use its singular matrices X,Y and Faber coefficients b_k; set M_k=Y*b_k(A)X, L_k=X*b_k(A)Y, and a²=sum_{k≥0}||M_k||_HS²>0. Write D_X,D_Y for the squared boundary HS norms of its two Hermitian diagonal fields and C for that of the cross field. The source proves

D_X,D_Y≤4a²/γ²,   2C≤D_X+D_Y,

C=a²+R,   R=3||M_0||_HS²+sum_{k≥1}||L_k||_HS².

Define E_X=4a²/γ²−D_X, E_Y analogously, and E_B=D_X+D_Y−2C. All these and R are nonnegative, and simple cancellation gives the **exact** identity

E_X+E_Y+E_B+2R=2(4/γ²−1)a².                         (6)

In particular R/a²≤4/γ²−1, and E_B/a²≤2(4/γ²−1), independently of n, coefficient size, and degree. For γ≥2−ε with 0≤ε≤1, R/a²≤4ε. Thus the normalized backward moments and zero-frequency cross matrix are O(√ε). The HS norm is unnormalized, exactly as in the source.

This is a proved residual statement for the genuine complete source, not a new geometric rigidity theorem. Passing from (6) to a disk estimate would require an inverse inequality for the entire certificate, not just keeping more signs in the proof. As Ω shrinks toward W(A), the resolvent/Faber normalizations can change or diverge; no uniform inverse bound is supplied. Equation (6) does not establish Q4(r), and is classified as technical source bookkeeping rather than a substantial finding.


## Completed frontier/experiments/i238_crouzeix_stability/reading-and-failures.md
# I238 — reading, exclusions, and failures

## Scope and operating record

Only I238's five assigned files were written. Work was restricted to openai-proof-research. No agents were spawned; no live sibling reports or shared ledgers were read; no staging, commits, publication, research code, tests, numerical experiments, parameter scans, snapshots, or seals were made. Short Python invocations performed retrieval, text extraction, metadata lookup, and hashing only. Mathematical checks were analytic.

Read AGENTS.md and sources/upstream.json in full; catalogue family 325 at CONTENTS.md lines 7929–7947, with a small surrounding range for context. The source revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All pinned theorems and lower operations were accepted as stipulated; provenance matching was not a source truth audit.

The only old discovery content read was the opening 65 lines of I39 and I130, plus a targeted case-insensitive Crouzeix/numerical-range/spectral-set search in those two files, which returned no matches. I39's opening is about spin-chain gaps and SK dynamics. I130's opening concerns harmonic growth and the earlier kernel audit. No historical replay or inherited ledger counts are used. The user-provided count remains nine.

## Pinned primary reading

Both family-325 companions were retrieved at pinned raw URLs and their Git blobs matched the preprints tree. Exact URLs, SHA-256 values, Git blobs, and bytes are in input-authentication.json. Their full TeX is retained inside literature.md; storing full TeX is not a claim that every collar or bibliography line was mathematically inspected.

1. **A direct proof of the complete Crouzeix inequality.** Read introduction and Theorem `thm:main`; all of Section 2, including `lem:faber` and `prop:coefficients`; all of Section 3, including `lem:resolvent`, `thm:domain`, both multiplication orders, the reciprocal coefficient weights, Parseval identities, and positive-block trace comparison; Section 4's `lem:approx` and final limiting/sharpness proof. The appendix's standalone conformal-collar construction is not a new dependency; its theorem is stipulated. The already-proved statements cover arbitrary finite base dimension, coefficient size, and degree, including point/segment numerical ranges.
2. **The complete Crouzeix theorem: optimal similarity and a common positive boundary representation.** Read Section 1's `thm:structural` and `thm:representation`; all of Sections 2–5, including metric attainment, `prop:density`, `prop:extremal`, `input:analytic`, `prop:projection`, the two density systems, and `lem:comparison`; read `cor:hilbert` and its full finite-compression/holomorphic-approximation proof. The repeated exterior computations were compared at the operation level. The companion supplies the optimal metric and one positive density, but does not assert a quantitative disk-rigidity theorem.

The direct proof's only shortfall terms available without new work are residual coefficient and block inequalities. Their smallness is not, by itself, an inverse estimate for numerical-range geometry. In particular, omitting constant terms or reversing one multiplication order would not produce a valid complete stability theorem.

## External primary reading

- **Åhag–Czyż–Virtanen, arXiv:2608.27346v3 (9 September 2026).** Extracted and fully read Sections 9 and 11, including all proofs. Section 9 gives the scalar square-function equality theory, the explicit 8√ε approximation to a reducing nilpotent block (Corollary 9.9), and optimized scalar/tuple estimates. Section 11 gives scalar polynomial equality classification, complete equality through base dimension three, the inverse-algebra criterion (Lemma 11.6), and the exact algebra-generation geometry theorem (Theorem 11.7). The paper is external literature, not an extra stipulated pinned manuscript. Its stronger scalar stability theorem is cited explicitly in Theorem Q.
- **Li, arXiv:2002.01027v1, Section 2.1.** Fully read the extracted two-by-two portion. It already supplies the elliptic conformal extremizer and its uniqueness. A simple two-by-two eccentricity calculation would be an extension of an explicit old formula, not substantial fresh work. No quantitative claim here uses the initial series formula's parameter convention.
- **Badea–Crouzeix–Delyon, arXiv:math/0501184, Section 5.2.** Retrieved the primary PDF, extracted and fully read Theorem 5.2, its proof, Corollary 5.3 and its proof, and Remark 5.1. This already provides the complete two-dimensional elliptic similarity, including repeated eigenvalues, and the common scalar/complete constant. It confirms that an ellipse-only complete estimate is not a fresh operator-class bridge.
- **Jin, Rigidity at the Extremal Crouzeix Constant, Preprints.org 202609.0079v2.** Read the main theorem/proof and all of Section 9 through its explicit statement that the stability modulus is nonconstructive. The retained web-rendered proof continuation includes Proposition 7's boundary-spectrum reduction and compactness argument and Theorems 2–3. The theorem is scalar; it gives no explicit exponent or uniform-in-base-dimension modulus. I do not attribute complete disk rigidity to it.

Search results also located work on numerical-radius partial smoothness, half-radial matrices, and weighted shifts. Those snippets were used only to avoid obvious claims of novelty; no theorem from them is used. They were not represented as fully read papers.

## Failures and corrected directions

1. **Whole-operator Jordan rigidity.** False without qualifications: an extremal block can be summed with arbitrary blocks inside the same disk. Multiple extremal blocks also remain extremal. This defeats a claim about closeness of the entire A to one 2×2 matrix.
2. **A two-by-two complete improvement as a new finding.** Rejected on prior-art grounds, after reading BCD and Li. The complete elliptic similarity is already explicit. No asymptotic parameter scan was performed.
3. **Scalar output rigidity at arbitrary coefficient size.** False, even for degree one and base/coefficient size two. P(z)=[[0,z],[1,0]] at A=[[0,2],[0,0]] is exactly extremal; P[A] is the irreducible weighted chain with weights (1,2,1). Its maximal singular vector has nonzero second iterate. The square-function quadratic form equals 9/4, rather than at most 2. The full computation is in analytic-attempt.md.
4. **“Complete” diagonalizable strictness by importing the scalar proof.** Not claimed. The inspected external paper gives complete strictness/conditioning consequences through base dimension three, but its scalar square-function route does not justify arbitrary matrix-valued witnesses. The counterexample in item 3 shows why a naive amplification of the intermediate theorem fails.
5. **Unconditioned transfer through A=q(p(A)).** Existence of q alone is not a quantitative hypothesis. The Crabb C_2 family p_δ(z)=(z²+δz)/(1+δ) has inverses whose normalized coefficient bound diverges. Theorem Q pays this conditioning explicitly; no eigenvector conditioning is silently assumed.
6. **Generic compactness as an explicit exponent.** Rejected. It does not yield a numerical power law. An effective algebraic inequality would still require exact complete rigidity at the relevant zero set, which has not been proved here in dimension four.

## Retrieval issues

The first html-extraction attempt used BeautifulSoup, which is not installed. It was replaced by Python's standard HTMLParser; no environment or package was modified. Direct urllib retrieval of the versioned Preprints.org page and of the Rennes BCD PDF returned HTTP 403. Jin was read through the web tool; BCD was successfully fetched from arXiv. The unavailable arXiv HTML request for Li v2 was replaced by the available v1. No primary-source inference relies on an inaccessible page's search snippet. These are retrieval limitations, not mathematical objections to source truth.

## Assessment

One pivot was made: from unrestricted/elliptic and scalar-output rigidity to bounded inverse reconstruction for scalar quadratic witnesses. The latter yields a complete explicit proof but is a restricted quantitative continuation of known scalar operations. It does not resolve Q4(r), the retained complete-geometry problem, and it is not nominated as the tenth substantial finding. The new obstruction and the restricted theorem should be retained as useful mathematics, without changing the count.
