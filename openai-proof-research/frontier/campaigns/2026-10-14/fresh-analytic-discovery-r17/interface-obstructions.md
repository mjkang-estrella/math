# Exact obstructions in the family 089 screen

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Status: pre-freeze research, not a nominated substantial result. These are
counterexamples to proposed proof operations, not counterexamples to the
clique-sum closure conjecture. No campaign count or proof verdict follows.

## 1. A finite uniform scalar reservoir would imply a Hilbert embedding

Let a finite metric space (X,d) have random real functions f_1,...,f_N,
each L-Lipschitz for every outcome, with

    E sum_i |f_i(x)-f_i(y)| >= a d(x,y).

Subtract f_i(x_0) and regard F(x)=(f_i(x)) as an element of
L2(Omega; R^N). Cauchy--Schwarz and the deterministic Lipschitz bounds give

    (a/sqrt(N)) d(x,y) <= ||F(x)-F(y)||_2
                         <= sqrt(N) L d(x,y).

Thus the Hilbert distortion is at most NL/a. If the lower bound is stated
for the average N^{-1} sum_i, the distortion bound is L/a instead.

Here is a self-contained classical diamond obstruction. Start with one
edge of length one. At each stage replace every edge uv of length ell by
u-a-v and u-b-v, all four new edges of length ell/2. Let D_h be the
result after h stages. Distances between retained vertices do not change
under replacement. For each replacement, d(a,b)=ell, including in D_h:
any path leaving that diamond must pass through u or v, and each of a,b
is at distance ell/2 from either endpoint. The graphs are planar.

For Hilbert vectors U,V,A,B, the parallelogram identity gives

    ||U-A||^2 + ||A-V||^2 + ||U-B||^2 + ||B-V||^2
      >= ||U-V||^2 + ||A-B||^2.

Indeed the left side minus the right side is
||U+V-A-B||^2. Let F be a noncontracting embedding of D_h with Lipschitz
constant K. Write S_j for the sum of squared image lengths over the
4^j generation-j edges, viewed as pairs of retained vertices in D_h.
Summing the displayed inequality at generation j gives

    S_j >= S_{j-1} + 4^{j-1} (2^{-(j-1)})^2 = S_{j-1}+1.

Since S_0>=1 and S_h<=4^h K^2 (2^{-h})^2=K^2, we get K>=sqrt(h+1).
Consequently a fixed N,L,a scalar reservoir cannot supply the required
all-pairs lower bound even inside arbitrary planar bags. This does not
exclude cut-valued reservoirs or scalar functions with only averaged
edge control. The diamond argument is a classical antecedent, included
to make this diagnostic independent of an uninspected citation.

## 2. Perfect local laws can glue to a periodic collapse

For n>=5 let G_n have vertex set {1,...,n}, unit edges whenever
1<=|i-j|<=3, and bags B_i={i,i+1,i+2,i+3}. Each bag is a K4; successive
bags meet in a triangle. On each bag put mass 1/4 on each of the six
binary assignments with exactly two labels equal to one, and zero mass
on all other assignments. This is a symmetric cut measure of mass 3/2.
For any two bag vertices exactly four of those six assignments separate
them, so its cut metric is exactly one: it is isometric on the bag.

The trace on any separator triple assigns mass 1/4 to each of its six
nonconstant assignments and mass zero to its two constant assignments.
Hence adjacent traces agree exactly, including their total mass.

In Markov gluing, after any nonconstant triple is known, the next label
is forced: there must again be exactly two ones among the four labels.
For successive windows, subtracting the two equations saying their
label sums equal two gives omega_{i+4}=omega_i. The glued law is supported
on the six balanced four-periodic assignments, each with mass 1/4.
It follows that D_mu(i,i+4)=0 although d_G(i,i+4)=2.

Thus neither consistency, exact triangle traces, symmetry, nor isometric
local bag metrics suffices for a global lower bound. Padding every bag
law by the same masses at the two constant assignments does not fix this:
the resulting global components are constant or four-periodic and still
collapse i and i+4. This is already a bounded-treewidth example; the
pinned source theorem is unaffected because it constructs special laws
with reservations and uncertainty, rather than asserting all laws work.

## 3. Subtracting an existing cut metric need not leave metric edge lengths

On a triangle let ell(ab)=ell(bc)=1 and ell(ac)=2. Let D be the cut
metric of the singleton {b}, so D(ab)=D(bc)=1 and D(ac)=0. For every
epsilon>0,

    (ell-epsilon D)(ac)=2 > 2-2epsilon
       =(ell-epsilon D)(ab)+(ell-epsilon D)(bc).

For epsilon<1 all residual lengths are positive, yet violate the triangle
inequality. Therefore the proposed boundary-calibration step cannot
subtract an arbitrarily small already embedded cut metric and treat the
remaining desired edge lengths as exact metric data. Shortest-path
completion would change the target boundary lengths. This invalidates
that proposed construction, not every possible boundary calibration.

## 4. An L1-valued replacement has two separate compatibility problems

The source scalar update (Fi,Fj) -> ((Fi+Fj)/2+g,(Fi+Fj)/2-g)
preserves the signed particle sum and uses a common weak order on the
interface to preserve its entire threshold-cut trace. Its numerical
subset-sum invariant also works in a Banach space if one fixed pair is
updated in the whole space: apply every norm-one linear functional to
the vector differences. This observation alone supplies no trace update.

For an L1-valued map on the two-point interface {p,q}, set Fi(p)=0 and
Fi(q)=r_i on Omega={-1,1}^N with uniform measure, where r_i are its
independent coordinate signs. For any distinct i,j, their weak orders
on {p,q} disagree on half of Omega. Thus no two of arbitrarily many
particles have a common coordinatewise weak order. The scalar k!
pigeonhole step cannot be carried over with the same finite bound.
Independent sign changes in each particle could align these orders,
but they do not preserve the signed sum used by the numerical invariant.

Choosing the updated pair separately in each L1 coordinate avoids that
pigeonhole issue but destroys the asserted norm bound. The following
finite construction shows this exactly. Work in l1^T with three particles
on two vertices p,q at distance one, all initially zero. At time t use
the perturbation g_t(p)=0, g_t(q)=e_t, of Lipschitz norm one. In coordinate
t update particles 1,2 by the scalar averaging-plus/minus rule. In every
other coordinate update particles 2,3; the perturbation there is zero.
In each coordinate the signed particle sum is preserved. Nevertheless,
after time t, particle 1 has value e_1+...+e_t at q and zero at p, hence
Lipschitz norm t. At old coordinates particle 1 is never touched; at the
new coordinate both updated values were zero. All updates can have the
interface {p}, where every particle vanishes. Thus the failure does not
come from violating interface compatibility.

One may check these operations on finitely many coordinates, so no
measurability, infinite-dimensional or limiting issue is involved. The
source invariant controls a fixed pair of vector-valued particles per
update; it does not justify coordinate-dependent pair choices with only
an L1 bound on each incoming perturbation.

## Unpaid operation and disposition

The genuinely missing step is a reservoir for arbitrary planar pieces
with bounded clique interfaces which simultaneously preserves compatible
boundary cut laws, has a depth-independent edge upper bound, and retains
enough conditional separation through arbitrarily long chains. The
source's scalar particles pay these requirements for bounded whole-bag
cardinality. Merely substituting bounded interface cardinality leaves
the within-bag lower bound, reservoir compatibility and accumulated
variation unpaid. The examples above rule out three natural shortcuts.

This screen has not supplied a tractable new mechanism for that step.
The familiar full clique-sum closure question is therefore not frozen as
a new candidate. No weaker subclass, conditional lemma, or these simple
diagnostics is substituted for a substantial campaign result.
