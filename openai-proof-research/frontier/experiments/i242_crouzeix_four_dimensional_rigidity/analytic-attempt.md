# I242 — early mathematical notes

Pinned theorems are accepted at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No scalar output-rigidity statement is amplified.

Let x=vec(X), y=vec(Y) be a maximal singular pair for a normalized complete witness. In the direct proof, write H(t)=R(t)+R(t)* and D=XX*−YY*. The pointwise positive-block slack is exactly

tr(ΔJΔJ)=tr(HDHD)=||H^(1/2) D H^(1/2)||_HS².

Thus zero slack implies that ran(H) is totally isotropic for D. Vanishing backward coefficients also gives X*Y=0 and X*A^kY=0 for all k≥1, because the Faber polynomials span the ordinary polynomials. The ranges of X and Y are consequently orthogonal. If H has rank n−1 at one regular boundary point, the inertia bound forces rank X=rank Y=1. The singular vectors then give a scalar polynomial p(z)=v*P(z)u with ||p(A)||=2 and sup_W|p|≤1. Existing scalar geometric rigidity would now apply to p; this is a reduction of the complete witness, not scalar output rigidity for P[A].

Unpaid at this initial stage: passing zero residual to a regular boundary arc with bounded nonzero normalization; treating n=4 when every maximal support eigenvalue is multiple. A boundary eigenvalue of A is reducing and can be split off, but this alone does not license replacing the full numerical range by the smaller block's range.

## Second partial note: a route beyond the original degree restriction

Take an irreducible reducing block B of A on which ||P[B]||=2. The stipulated bound implies sup_{W(B)}||P||=1. As B is irreducible and has size at least two, every eigenvalue lies strictly inside W(B): a boundary eigenvector is a common eigenvector of B and B*. Thus the direct proof can be passed to W(B) with a uniformly bounded resolvent.

The needed uniform exterior bound is elementary. For a convex analytic domain with normalized exterior map h(z)=cz+c0+..., c>0, convexity gives Re(1+zh''/h')≥0. The exterior Herglotz formula gives

log(h'(z)/c)=2∫ log(1−ξ/z) dμ(ξ),

where μ is a probability measure on the circle. Hence |h'|≤4c. For a shrinking sequence with rD⊂Ω_j⊂RD, r≤c_j≤R. Subsequence weak convergence of μ_j gives strong L² convergence of these logarithms: their kth Fourier coefficients are −2 μ̂_j(k)/k, with uniformly summable squared tails. Exponentiation preserves convergence because their real parts are bounded above by log4. Hence h'_j converges strongly in L², which controls the resolvent fields and allows the exact nonnegative residual identity to pass to the boundary. This removes the previously unpaid normalization blowup for a fixed irreducible B.

For d≤4 an irreducible B has a direction where Re(e^(−iθ)B) has a simple largest eigenvalue. Otherwise largest and smallest eigenvalues are both multiple for every θ. For d≤3 this forces every pencil value scalar. For d=4, after centering, Hθ² is scalar for every θ. Thus H²=aI, K²=bI, HK+KH=2cI. Subtracting (c/a)H from K yields an anticommuting pair, unitarily equivalent to identical 2×2 pairs (or commuting matrices in the degenerate case), contradicting irreducibility.

At a simple support direction irreducibility makes the curvature radius strictly positive, by the second derivative formula for a simple Hermitian eigenvalue. There is therefore a genuine analytic boundary arc. The limiting resolvent field has rank d−1 on it. Zero block slack forces rank X=rank Y=1. Extract p(z)=v*P(z)u from the coefficient tensor factors. Then ||p(B)||=2, sup_{W(A)}|p|≤1. The external scalar polynomial equality classification gives p(z)=c(z−a)^k and W(B)=a+ρDbar, |c|ρ^k=1. Therefore W(A)⊂a+ρDbar; since it contains W(B), equality holds. This would prove exact complete disk rigidity for all finite polynomial degrees and coefficient sizes in base dimension at most four. The remaining work is a careful complete write-up and source reading, not a claimed modulus.

# Completed equality argument

The preceding two entries are contemporaneous partial notes. The argument below supersedes their unpaid steps. No positive-deficit power modulus is claimed.

## Statement

**Theorem E4 (complete polynomial disk rigidity).** For every integer 1≤n≤4, every A∈M_n(C), every finite integer m≥1, and every M_m-valued polynomial P of any finite degree, set M=max_{z∈W(A)}||P(z)||. If M>0 and ||P[A]||=2M, then W(A) is a nondegenerate closed disk. Moreover there are unit coefficient vectors u,v∈C^m such that the scalar polynomial p(z)=v*P(z)u satisfies

||p(A)||=2M=||P[A]||,  max_{W(A)}|p|=M.

More specifically, there is an irreducible reducing block B of A with ||p(B)||=2M. After writing W(A)=a+ρDbar, ρ>0, one has

p(a+ρz)=Mη z^k  (|η|=1, k≥1).

The exponent is at most deg P; no bound sharper than this is needed here. In particular, in Q4(r), for every 0<r<1 and every finite m, exact equality for degree at most two forces W(A)=Dbar. The minimum-enclosing-disk normalization identifies the disk uniquely; the inball assumption excludes degeneracy but is not otherwise needed for exact equality.

The theorem is conditional on the stipulated complete source bound and uses the external **scalar geometric** theorem of Jin, not a matrix amplification of a scalar output theorem. Its substantive new step is reduction of an exact complete witness to a scalar one.

## 1. Convex exterior maps: the limit is controlled

We give the limiting argument since setting γ=2 on a strictly enclosing domain would be invalid.

Let K be any compact convex body, and let Ω_j be analytic convex outer neighborhoods supplied by the pinned direct lemma `lem:approx`, converging in Hausdorff distance to K. Translate temporarily so that rDbar⊂K, r>0, and choose R with Ω_j⊂RD eventually. Normalize the exterior maps by

h_j(z)=c_j z+c_{0,j}+O(z^−1), c_j>0.

Then r≤c_j≤R. For the first inequality apply Schwarz's lemma to r/h_j(1/w), which maps D to D and has derivative r/c_j at zero. For the second apply it to 1/Φ_j(R/w), where Φ_j=h_j^−1 on the exterior of Ω_j; its derivative is c_j/R. Also |c_{0,j}|≤R by the mean of the boundary values.

The boundary tangent is izh'_j(z). Convexity and its counterclockwise orientation give

Re g_j(z)≥0 on T,  g_j(z)=1+zh''_j(z)/h'_j(z),  g_j(∞)=1.

The same inequality holds in the exterior by the harmonic minimum principle. The disk Poisson/Herglotz formula, applied after z↦1/z, gives a probability measure μ_j on T such that

g_j(z)=∫ (z+ξ)/(z−ξ) dμ_j(ξ).

Integrating the logarithmic derivative with value zero at infinity gives

L_j(z):=log(h'_j(z)/c_j)=2∫ log(1−ξ/z) dμ_j(ξ).                 (1)

The logarithm is the branch zero at infinity. Thus Re L_j≤2log2 and

|h'_j(z)|≤4c_j≤4R  (|z|≥1).                                  (2)

In particular the boundary maps are equi-Lipschitz. Normal-family compactness and equicontinuity give a subsequence converging locally uniformly outside D and uniformly on T to the normalized exterior map h of K. Here is the identification, to avoid hiding a boundary regularity assumption: the nonzero limiting leading coefficient makes the univalent limit nonconstant and univalent; its exterior image avoids int K by convergence of the Ω_j. Conversely, on every compact subset of C\K the inverse maps Φ_j form a normal family. Their possible limits have modulus strictly greater than one, by the maximum principle and their normalization at infinity, and are inverses of h. Hence the image is C\K. Uniform convergence on T and Hausdorff convergence of the boundaries identify h(T)=∂K. Equivalently this is the normalized exterior kernel theorem with the equi-Lipschitz boundary estimate (2).

For more explicit normal-family bounds in that inverse argument: h_j(z)−c_jz is holomorphic on the exterior including infinity, with boundary modulus at most 2R, so it has modulus at most 2R throughout. Therefore |Φ_j(w)|≤(|w|+2R)/r wherever Φ_j is defined. These bounds supply the required local compactness; convergence at infinity identifies the inverse branch.

Pass also to c_j→c and μ_j→μ weakly. In boundary L² the logarithm in (1) has Fourier coefficients

−2(∫ξ^k dμ_j)/k, k≥1.

Each coefficient converges, and the squared tail after N is at most 4∑_{k>N}k^−2, uniformly in j. Thus L_j converges strongly in L²(T). Since real parts are bounded above by log4,

|exp u−exp v|≤4|u−v|  whenever Re u,Re v≤log4,

as follows by integration along the segment between u and v. Consequently h'_j→h' strongly in L² and q_j=zh'_j→q=zh' strongly in L². The analytic derivatives inside the exterior identify the limiting boundary function as h'. This proof uses weak convergence only for scalar probability measures, followed by a proved strong Fourier estimate; it does not pass a quadratic residual through weak convergence.

Now suppose σ(B)⊂int K. On ∂Ω_j and ∂K the resolvents (zI−B)^−1 are uniformly bounded: all points lie in a fixed compact set separated from the finite spectrum. Uniform boundary convergence of h_j then gives uniform convergence of their resolvents. Hence

R_j=q_j(h_jI−B)^−1 → R=q(hI−B)^−1 strongly in L²(T),          (3)

and R_j are uniformly bounded in L∞ by (2). Their Hermitian parts H_j=R_j+R_j* converge strongly in L² to H=R+R*, with H≥0 almost everywhere. On any regular real-analytic boundary arc, h extends conformally by local reflection and q is a nonzero outward normal. On that arc,

(hI−B)* H (hI−B)=2 Re[bar q(hI−B)].                           (4)

This is precisely the direct source's original-matrix positive field, not the companion's mass-one density after similarity.

## 2. Passing the exact source residual to equality

Normalize M=1. First take a matrix B with σ(B)⊂int W(B), and a polynomial P with max_{W(B)}||P||=1 and ||P[B]||=2. Let x,y be any unit maximal singular pair, with P[B]x=2y and P[B]*y=2x. In the source convention write x=vec(X), y=vec(Y), so ||X||_HS=||Y||_HS=1.

Use K=W(B), the Ω_j above, M_j=max_{closure Ω_j}||P||→1, and F_j=P/M_j. The same x,y are a singular pair for F_j[B], with γ_j=2/M_j→2. For the jth Faber basis define

a_j²=∑_{k≥0}||Y*b_{k,j}(B)X||_HS²=||Y*R_j X||²_{L²(HS)}.

By (2)–(3), a_j is bounded. It is positive by the source pairing with F_j. No positive lower bound on a_j is required.

Explicitly put D_{X,j}=∫_T||X*H_jX||_HS² dτ, D_{Y,j}=∫_T||Y*H_jY||_HS² dτ and C_j=∫_T||Y*H_jX||_HS² dτ, with dτ=dt/(2π). These are the source's diagonal and cross norms. Define its nonnegative residuals

Rres_j=3||Y*X||_HS²+∑_{k≥1}||X*b_{k,j}(B)Y||_HS²,
E_{X,j}=4a_j²/γ_j²−D_{X,j}, E_{Y,j}=4a_j²/γ_j²−D_{Y,j},
E_{B,j}=D_{X,j}+D_{Y,j}−2C_j.

Keeping every term in the direct proof yields exactly

E_{X,j}+E_{Y,j}+E_{B,j}+2Rres_j
             =2(4/γ_j²−1)a_j².                              (5)

Every term is nonnegative. Since a_j stays bounded and γ_j→2, all terms on the left tend to zero. In particular X*Y=0.

Put D=XX*−YY*. With W=[X Y] and J=diag(I_m,−I_m), the source's positive block is Δ_j=W*H_jW, and the pointwise trace slack is

tr(Δ_jJΔ_jJ)=tr(H_j D H_j D)
                =||H_j^(1/2) D H_j^(1/2)||_HS².              (6)

By (3), tr(H_j D H_j D)→tr(H D H D) in L¹: expand the difference and use Cauchy–Schwarz and the bounded L² norms. Its integral is E_{B,j}→0. Since H≥0, (6) gives

H(t)^(1/2) D H(t)^(1/2)=0 for almost every t∈T.              (7)

Thus ran H(t) is a totally isotropic subspace for the Hermitian form D. This is the inverse information that the scalar nonnegative residual, by itself, did not previously expose.

For completeness all backward moments also vanish. With X*Y=0, the sum of squared coefficients of X*R_jY is exactly ∑_{k≥1}||X*b_{k,j}(B)Y||²→0. Equation (3) gives X*RY=0 in boundary L². Uniqueness of the exterior Hardy expansion gives X*R(z)Y=0 outside D. Since q(z)≠0 there, the resolvent expansion at infinity yields

X*B^kY=0 for every integer k≥0.                             (8)

Equation (8) is additional information; the rank argument below requires its k=0 case and (7), and makes no unjustified conclusion from (8) alone.

## 3. The actual inverse lemma: a simple support eigenvalue forces scalarization

**Lemma S.** In the setting of Section 2, suppose some open regular analytic boundary arc of W(B) has simple maximal support eigenvalue. Then rank X=rank Y=1, for every maximal singular pair used above.

Indeed (4) shows rank H=d−1 on this arc, where d is the size of B. Since X*Y=0, the positive and negative inertia indices of D are p=rank X and q=rank Y, with p,q≥1; its nullity is d−p−q. A totally isotropic subspace for a Hermitian form of that inertia has dimension at most

d−p−q+min(p,q)=d−max(p,q).

To see the bound, quotient its intersection with ker D and project the remaining isotropic space to the positive and negative spectral subspaces. Each projection is injective, so its dimension is at most min(p,q). Applying this to ran H and (7) gives d−1≤d−max(p,q). Thus p=q=1. There is a point of the arc where (7) holds because its preimage is an open circle interval of positive measure. ∎

Write x=ξ⊗u and y=η⊗v with all four factors unit. Then

p(z)=v*P(z)u,  η*p(B)ξ=y*P[B]x=2,

while |p(z)|≤||P(z)||. The complete bound at coefficient size one yields ||p(B)||=2 and max_{W(B)}|p|=1. This is a scalar **input witness extracted from a complete singular pair**. It does not assert any nilpotent reducing block for P[B].

## 4. Every irreducible block of size at most four has the required arc

Let B be unitarily irreducible of size 2≤d≤4. It is nonnormal and W(B) has interior. A boundary eigenvector would reduce B: if Bv=λv and ν supports W(B) at λ, positivity of sI−Re(barνB) and its zero quadratic form at v give B*v=barλv. Thus σ(B)⊂int W(B).

Suppose no Hθ=Re(e^−iθB) has simple largest eigenvalue. Replacing θ by θ+π shows its smallest eigenvalue is also always multiple. For d=2 or 3 this forces Hθ scalar for every θ, hence B scalar, a contradiction.

For d=4, subtract tr(B)I/4. Each Hθ has trace zero and either is zero or has precisely two eigenvalues +sθ,−sθ, each twice. Therefore Hθ² is scalar for every θ. Writing B=H+iK gives

H²=aI, K²=bI, HK+KH=2cI,  a,b≥0, c real.                  (9)

If H=0, B is normal; otherwise a>0. In a unitary basis H=√a diag(I₂,−I₂). Put K'=K−(c/a)H. It anticommutes with H and satisfies

(K')²=(b−c²/a)I=:δI, δ≥0.

Hence K'=[[0,C],[C*,0]], with CC*=C*C=δI₂. If δ=0, K'=0 and B is normal. If δ>0, C/√δ is unitary; conjugating separately on the two eigenspaces of H makes C=√δ I₂. Reordering the basis gives a direct sum of two identical 2×2 pairs for H,K', and hence for B. This contradicts irreducibility. A simple largest eigenvalue therefore exists.

Such simplicity persists on an interval. Let λ(θ) be the simple top eigenvalue, v its unit eigenvector, and v_j an orthonormal eigenbasis for the other eigenvalues λ_j. Elementary differentiation of the eigenvalue equation gives

λ+λ''=2∑_{j≠top}|v_j*H'_θv|²/(λ−λ_j).                       (10)

Every denominator is positive. If the right side vanished, v would be a common eigenvector of Hθ and H'_θ, hence of B and B*, again contradicting irreducibility. Thus λ+λ''>0 throughout the interval. The exposed point

z(θ)=e^{iθ}(λ+iλ'),  z'(θ)=ie^{iθ}(λ+λ'')

parametrizes an open regular real-analytic arc, with simple support eigenvalue. Lemma S applies.

The elementary argument (9) is deliberately restricted to size four. It does not claim Kippenhahn's conjecture in higher dimensions or deduce simplicity from a repeated-factor theorem.

## 5. Finishing the theorem, including reducible A and the outer geometry

Decompose A unitarily into irreducible reducing blocks. Evaluation is their orthogonal direct sum. Some block B satisfies ||P[B]||=2. Size-one blocks have evaluation norm at most one, so 2≤dim B≤4. Because W(B)⊂W(A),

2=||P[B]||≤2 max_{W(B)}||P||≤2.

Thus max_{W(B)}||P||=1. Sections 1–4 extract unit u,v and p=v*Pu with ||p(B)||=2 and max_{W(A)}|p|≤1.

Now invoke the actual **scalar geometric** theorem: Jin, *Rigidity at the Extremal Crouzeix Constant*, v2, Theorem 1, says ψ(B)=2 implies W(B)=a+ρDbar for some ρ>0. The scalar bound and the polynomial p give ψ(B)=2. No assertion about the operator P[B] is imported.

Here is the additional scalar fact needed to exclude an outer summand, with its proof. Put T=(B−aI)/ρ and g(z)=p(a+ρz). Then σ(T)⊂D, ||g(T)||=2 and ||g||_D=1. Prescribe the finite contiguous spectral jets that determine g(T). Their minimum Schur interpolation norm is one: a smaller-norm interpolant would, by polynomial approximation on smaller disks followed by the stipulated scalar bound, give ||g(T)||<2. Jin's Lemma 4, whose finite Schur recursion and uniqueness proof were read in full, says the norm-one interpolant is unique and is a finite Blaschke product. Hence g itself is a finite Blaschke product. A polynomial finite Blaschke product has every zero at zero, because a nonzero zero α would produce a pole at 1/barα that cannot cancel against a numerator zero in D. Therefore

g(z)=η z^k, |η|=1, k≥1.

The exponent is positive because a constant cannot evaluate with norm two. Since |p(z)|≤1 on W(A), this formula forces W(A)⊂a+ρDbar. The reverse inclusion is W(B)⊂W(A). Consequently W(A)=a+ρDbar and ||p(A)||=2. Rescaling P restores M and proves Theorem E4. ∎

As an independent scalar check on the last paragraph, Jin's Lemma 5 gives strict domain monotonicity for the scalar H∞ calculus. If W(A) were strictly larger than the disk W(B), both the smaller-disk and larger-domain calculus of B would have norm two by the same p, contradicting that lemma. The monomial argument above is retained because it also produces the explicit scalar symbol and uses no compactness modulus.

## 6. Companion / operator-valued maximum route

The structural companion's `thm:representation` and `prop:density` use one minimizing S and one positive density Λ for all coefficient sizes. At equality in its contractive evaluation, the dilation isometry V and multiplication M_F satisfy

M_F Vx=Vy,  M_F*Vy=Vx,

or, fiberwise, (I⊗F)x_Λ=y_Λ and (I⊗F*)y_Λ=x_Λ. These are genuine complete equalities (the companion's `eq:fiber-equality`). They permit nonconstant matrix-valued isometric channels and do not make F scalar. A matrix Schur function can have a constant unitary summand; saturation of its norm does not make the full matrix function constant. Nor does the disk contraction model alone identify the numerical range of the original, nonsimilar matrix.

The original-matrix field H and the inertia bound in Lemma S provide exactly the missing input. Once rank-one coefficient factors have been forced, the maximum/Schur route becomes scalar and its monomial conclusion is legitimate. Before this rank reduction it would repeat the failed scalar amplification. Thus the second route is useful for source contract checking and for the final scalar step, but is not presented as a separate unproved complete equality classification.

## 7. Positive deficit remains unpaid

Theorem E4 proves Q4(r) at ε=0, for all finite m and even all finite polynomial degrees. It does **not** prove constants C_r,ε_r>0 with d_H(W(A),Dbar)≤C_r ε^(1/4) for 0<ε≤ε_r.

The precise quantitative gap is a uniform version of the inverse argument across reducible limits. For one fixed irreducible B, (5)–(7) and a boundary arc with a fixed lower bound on its nonzero support gaps control proximity of D to rank-(1,1) inertia data. Q4(r)'s inball and enclosing-disk normalization do not supply a uniform lower bound for the support gap, arc length, spectral distance to the boundary, or separation of reducing blocks. These quantities can collapse when B approaches a reducible matrix even though the inball remains fixed. An estimate must resolve those collapsing strata and transport the approximate scalar witness to the **full** numerical range with a paid exponent. Neither (5) nor compactness alone pays this estimate. No claimed quarter-power law or numerical parameter search is made.
