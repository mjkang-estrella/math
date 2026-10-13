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
