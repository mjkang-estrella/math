# Exact structured tests of the small-maximum branch

These are author calculations for the unchanged all-dimensional entropy stability problem. They neither prove global entrance (GR) nor produce a counterexample to it. Unlike a conditional reduction, they test concrete diffuse tensors with B=I and compute the total defect. All norms are unnormalized.

## 1. A barrier for every harmonic cubic

Put c_k=Σ_i T_iik, the trace vector. Full symmetry gives

Σ_(i<j)[X_i,X_j]_ij=(||c||²−tr B)/2.

Indeed the sum over ordered i,j of the first product in the commutator is Σ_k(Σ_i T_iik)², and that of the second is Σ_ijk T_ijk²=tr B. The unordered sum is half the ordered sum. Every real skew matrix contributes both its ij and ji entries to its Frobenius square. Cauchy–Schwarz therefore gives, for m≥2,

C≥(tr B−||c||²)²/[m(m−1)].                              (1)

In particular if T is harmonic (c=0) and B=I, then C≥m/(m−1)>1. Consequently no sequence of harmonic cubics with exact B=I can have R→0, even if its maximum cubic value tends to zero. This is a genuine absolute residual barrier for the entire harmonic class.

This does not handle general tensors. For B=I, the projection formulation gives ||c||²≤m, and exact odeco tensors have ||c||²=m. The diffuse unital family in§3 also has ||c||² equal to its dimension, so trace alone cannot settle GR.

## 2. Traceless symmetric-matrix Jordan tensors: diffuse maximum, extensive defect

Let d≥3 and V be the real traceless symmetric d×d matrices, with inner product tr(AB). Its dimension is m=(d−1)(d+2)/2. The fully symmetric cubic J0(A,B,C)=tr(ABC) represents the product

A∘B=(AB+BA)/2−tr(AB)I/d.

For a diagonal A with tr A=0 and tr A²=1, its multiplication operator has eigenvalues (a_i+a_j)/2 on off-diagonal symmetric matrix units. Their squared sum is (d−2)/4. On the traceless diagonal subspace its squared Frobenius norm is tr(P diag(a) P diag(a))=1−2/d, where P=I−11^t/d. Therefore

||L_A||F²=κ=(d+4)(d−2)/(4d).

Orthogonal conjugation diagonalizes every A, and polarization gives <L_A,L_B>=κ<A,B>. Thus J=J0/sqrtκ has B(J)=I exactly.

The maximum of tr(A³) under tr A=0 and tr A²=1 is (d−2)/sqrt(d(d−1)). For completeness, the Lagrange equations make each eigenvalue a root of one common quadratic, hence there are at most two distinct eigenvalues. If the positive value has multiplicity k, the positive cubic value is (d−2k)/sqrt(d k(d−k)); this is maximal at k=1 (the square decreases with k for 1≤k≤d/2). Reversing sign handles the other extrema. Hence

lambda(J)=2sqrt(d−2)/sqrt((d−1)(d+4)) →0.                (2)

We compute its defect without asymptotics. For A,B∈V,

[L_A,L_B]X=(1/4)[[A,B],X]−( <B,X>A−<A,X>B )/d.          (3)

Let (A_a) be an orthonormal basis of V, K_ab=[A_a,A_b], and W_ab=A_a⊗A_b−A_b⊗A_a. Three sums are needed:

Σ_(a<b)||K_ab||F²=md/2,
||ad_K on V||HS²=(d+2)||K||F²,
<ad_[A,B], A⊗B−B⊗A>HS=2||[A,B]||F²

for orthonormal A,B. The first follows by diagonalizing a fixed A and summing (a_i−a_j)²=d over all off-diagonal symmetric basis matrices, then dividing the ordered double sum by2. For the second, take K to generate rotation in one coordinate plane: the traceless symmetric 2×2 block contributes8, while the mixed entries with each remaining coordinate contribute2, giving2(d+2) when ||K||F²=2. Orthogonal block diagonalization and cancellation of cross terms extend this quadratic identity to every skew K. For the third, invariance of trace gives <A,[[A,B],B]>=||[A,B]||F², and the two rank-one terms give twice this value. Also Σ_(a<b)||W_ab||HS²=m(m−1).

Expanding (3) consequently yields

C(J0)=md(d+2)/32−m/2+m(m−1)/d².

Divide by κ², since commutators scale quadratically under cubic rescaling. Substitution of m and κ simplifies to

C(J)=m(d²+8)/[2(d+4)(d−2)] ~ m/2.                       (4)

Thus this explicit small-maximum family does not approach the zero set in residual. Its trace vector is zero (tr L_A is a constant multiple of tr A), consistent with§1.

## 3. Exact unit and B=I still do not force a large maximum

The preceding harmonic barrier might suggest extracting a unit from the trace vector. That alone is insufficient. Let J be the normalized tensor in§2, N=m+1, and introduce a coordinate e0. Set

T000=b=1/sqrt N,
T0ij=b δij (tangent i,j),
T00i=0,
Tijk=sqrt(1−2/N) Jijk (all tangent).

Extend by full symmetry. Since J has B=I and trace vector zero, direct contraction gives B(T)=I. Its zero slice is b I_N, so sqrt N e0 is an exact unit. The trace vector is sqrt N e0 and has squared norm N.

For t²+||A||²=1,

T((t,A)^3)=b(t³+3t||A||²)+sqrt(1−2/N) J(A³).

The absolute first term is at most sqrt2/sqrt N, and the second at most lambda(J). Consequently lambda(T)→0. Exact existence of a unit, even together with B=I, cannot replace the small-commutator hypothesis.

The defect remains large. Write s²=1−2/N. All commutators with slice0 vanish. For tangent slices the lower block is s²[J_i,J_j]+b²(Eij−Eji), and the upper blocks vanish. The trace-vector identity of§1 for J gives

Σ_(i<j)<[J_i,J_j],Eij−Eji>=−m.

Hence

C(T)=s⁴ C(J)−2s²b²m+b⁴m(m−1)
    =(1−2/N)² C(J)−m(m−1)/N² ~m/2.                     (5)

This is not a counterfamily to GR. It excludes the proposed shortcut 'B=I plus an exact unit implies a dimension-independent maximum.'

## 4. Finite abelian group tensors

For a finite abelian group G of order n, set T_abc=n^(-1/2)1{a+b+c=0} in its standard orthonormal coordinate basis. It is fully symmetric. Each slice is a permutation reflection divided by sqrt n, so X_a²=I/n and B=I. The products X_a X_b and X_b X_a are opposite translations divided by n. If 2(a−b)=0 they coincide; otherwise the difference of the two permutation matrices has squared Frobenius norm2n. Therefore

||[X_a,X_b]||F²=0 or 2/n,
C=n−|G[2]|.

If G is not an elementary2-group, its2-torsion subgroup has size at most n/2, so C≥n/2. If it is an elementary2-group, C=0 and this is an exact odeco tensor after real Fourier transformation, as the exact characterization also implies. This basic group-algebra route supplies no diffuse small-residual counterfamily.

## Remaining issue

The structured tests support an absolute defect barrier for diffuse examples, but do not prove one for arbitrary symmetric cubics. The missing result is still a dimension-independent c>0 and rho>0 such that B≈I and C≤rho² force lambda≥c, or an actual family violating it. The exact unital example shows that the trace vector cannot by itself finish that step. No unsupported global estimate is inferred from these examples.
