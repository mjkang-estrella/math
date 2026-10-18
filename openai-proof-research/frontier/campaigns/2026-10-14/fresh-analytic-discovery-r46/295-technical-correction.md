# Uniform correction of a small associativity defect — technical screen

Author: Myeongjin Kang, original prose CC BY 4.0. This is an author-side
calculation, not a nominee or independent review. The argument and its
scope were recognized as a standard cohomological/Newton transfer before
this proof was assembled; no pre-exploration candidate freeze is claimed.

## Exact technical statement

There are absolute constants ε>0 and C<∞ such that for every complex von
Neumann algebra M, with its ordinary norm and multiplication m, and every
bounded complex bilinear ν:M²→M satisfying ||ν−m||≤ε, there is an invertible
bounded complex linear T:M→M with

    ||T−I||≤C||ν−m||,  ||T||,||T⁻¹||≤2,
    ||ν−T m(T⁻¹·,T⁻¹·)||≤C||A_ν||,

where A_ν(x,y,z)=ν(ν(x,y),z)−ν(x,ν(y,z)). No associativity, normality,
complete boundedness, *-compatibility, common unit, finite-dimensionality,
separability or tracial hypothesis is imposed on ν. If A_ν=0, the last
inequality gives exact algebraic conjugacy. This is not a spatial-unitary
conjugacy theorem and does not claim T preserves a prescribed involution.

The sole new truth premise is source295, thm:main: ordinary bounded
Hochschild cohomology H_b^k(M,M) vanishes in all degrees k≥2. Its
introduction explicitly identifies perturbation stability as an application
of this cohomology. The remaining argument is standard normed cohomological
correction and finite stopping of a Newton iteration.

## Uniform bounded primitives

For every fixed k≥2 there is a constant C_k, uniform over all complex von
Neumann algebras, such that every bounded k-cocycle f has a primitive g
with ||g||≤C_k||f||. Suppose otherwise. Choose M_j and cocycles f_j of
norm at most one for which every primitive has norm greater than j.
On the bounded direct product M=∏^{ℓ∞}M_j, define F coordinatewise from
the f_j. This is a bounded k-cocycle of norm at most one. Source295 gives
a bounded primitive G. Insert inputs supported in coordinate j and take
the jth output coordinate. This produces a primitive g_j of f_j with
||g_j||≤||G||, a contradiction. Coordinate insertion is not unital but
is multiplicative, and each outer module action in the differential has
the correct jth coordinate. No bounded linear selection of primitives is
asserted or needed. Enlarge C_2,C_3 to be at least one.

## One correction step

Use the source differential δ, whose degree-two norm is at most four.
Write ν=m+φ, η=||φ||≤1 and D=||A_ν||. Direct expansion gives

    A_ν=−δφ+φ(φ(·,·),·)−φ(·,φ(·,·)),
    ||δφ||≤D+2η²,  D≤4η+2η²≤6η.

Since δ²=0, δφ is a 3-cocycle. Choose a 2-cochain ρ satisfying

    δρ=δφ,  ||ρ||≤C_3(D+2η²)≤8C_3η.

Then φ−ρ is a 2-cocycle. Choose a bounded linear h with

    δh=φ−ρ,  ||h||≤C_2(1+8C_3)η=:Kη.

If Kη≤1/2, set g=I−h and ν'=g⁻¹ν(g·,g·). The exact identity

    ν(gx,gy)−g(xy)
      =ρ(x,y)+m(hx,hy)+φ(gx,gy)−φ(x,y)

shows, with B=4C_3+4K²+4K,

    η':=||ν'−m||≤2C_3D+Bη².                                  (1)

Indeed ||g⁻¹||≤2 and
||φ(g·,g·)−φ||≤η(2||h||+||h||²). Associators transform exactly:

    A_{ν'}=g⁻¹ A_ν(g·,g·,g·).                                (2)

This is the nonlinear error term that cannot be dropped when the input
product is only approximately associative.

## Uniform iteration and stopping

Fix

    ε≤min(1,1/(2K),1/(4B),(log 2)/(10K)).

Start ν_0=ν, T_0=I, η_0=||ν−m|| and D_0=||A_ν||. As long as
η_j>16C_3D_0, perform the preceding step and set T_{j+1}=T_jg_j.
Inductively, η_j≤2^(−j)η_0 while the iteration continues. To verify
the induction together with the distortion bounds, note that

    Σ_{i<j}||h_i||≤2Kη_0,
    ||T_j||≤exp(2Kη_0),  ||T_j⁻¹||≤exp(4Kη_0).

The second inequality uses (1−u)⁻¹≤exp(2u) for u≤1/2. Equation (2)
for the cumulative T_j gives

    D_j≤||T_j⁻¹||||T_j||³D_0≤exp(10Kη_0)D_0≤2D_0.

Consequently (1), the continuing condition, and Bη_j≤1/4 imply

    η_{j+1}≤4C_3D_0+Bη_j²≤η_j/2.

This proves the simultaneous induction. Also
||T_j−I||≤exp(Σ||h_i||)−1≤4Kη_0, and both T_j and its inverse
have norm at most two.

If D_0>0, the iteration stops after finitely many steps with
η_j≤16C_3D_0. Pulling m back by T_j gives an exactly associative
product μ=T_jm(T_j⁻¹·,T_j⁻¹·), and

    ||ν−μ||≤||T_j||||T_j⁻¹||²η_j≤128C_3D_0.

If the stopping condition holds initially, use T=I. If D_0=0, the
iteration either reaches m exactly or continues with η_j→0. The products
T_j and their inverses converge in operator norm because Σ||h_j||<∞;
their limits are mutually inverse. Passing to the limit in
ν_j=T_j⁻¹ν(T_j·,T_j·) gives exact conjugacy. The zero algebra is trivial.
Taking C=max(4K,128C_3) proves the statement.

## Why this is not nominated

Raeburn–Taylor (1977), *Hochschild cohomology and perturbations of Banach
algebras*, explicitly states the H²=H³=0 associative perturbation theorem.
Only its publisher abstract was accessible in this round; the PDF request
returned403, so its operative proof is not claimed read.

Kochanek, arXiv:2303.07869v1, was read through the full proof of Theorem1.
Its Lemmas2–3 and Proposition7 explicitly give a quadratic improvement
plus an additive associativity-defect term, followed by finite stopping
in place of convergence. It assumes an amenable domain and constructs a
right inverse from an approximate diagonal. Here source self-cohomology
supplies the primitive instead. Uniformization by bounded products and
stopping when the residual is a constant multiple of the defect are
standard transfers. No new substantial mechanism or literature priority
is asserted by changing the domain class or recording a linear residual
bound. In particular this is not promoted as a solution of the general
AMNM/Ulam-stability problem.

## Exact boundary of the argument

For a genuine reference homomorphism π₀:M→N between different algebras,
linearization uses cochains with coefficients in the π₀-induced N-bimodule.
For an approximately multiplicative π, the proposed π-induced actions are
only approximate actions: their coboundary need not square to zero.
Source295 gives self-coefficients M, not arbitrary N-bimodules.
There is no automatic conditional expectation or bounded bimodule
projection allowing replacement of N by π(M). Our proof stays near the
identity on one underlying Banach space and uses the fixed original
multiplication differential. It does not prove global stability of arbitrary
almost homomorphisms, spatial Kadison–Kastler stability, or uniform correction
in completely bounded norm. No such stronger scope has been frozen.

For an explicit check of the latter distinction, take M=N=ℂ² with coordinate
multiplication, π=cI with c≠0,1 arbitrarily close to 1, and h swapping the
two coordinates. Put D_π(x,y)=π(x)π(y)−π(xy). The usual proposed differential
satisfies

    δ_π² δ_π¹h(x,y,z)=D_π(x,y)h(z)−h(x)D_π(y,z).

At (x,y,z)=(e₁,e₁,e₂) this equals c(c−1)e₁≠0. Thus applying source
cohomology to this approximate differential is literally invalid. This
example only rejects that formal shortcut; it is no obstruction to an
actual stability theorem or to Kochanek's controlled approximate complexes.
The source introduction also records classical extended cobounding for
M-valued cocycles with B(H)-valued primitives. We do not claim that known
operation is absent; it does not provide arbitrary N-valued primitives.
