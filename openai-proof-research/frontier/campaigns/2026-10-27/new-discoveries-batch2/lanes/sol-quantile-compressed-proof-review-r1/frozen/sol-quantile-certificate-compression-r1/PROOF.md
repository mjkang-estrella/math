# Continuous certificate compression (ordinary mathematics only)

This is a refinement of the held candidate, not a new discovery, manuscript,
formal certificate, acceptance, or novelty clearance. The original lane is untouched.

## Statement and source class

For a tuple of cdfs, D_n denotes all laws of sums over arbitrary couplings with
those marginal cdfs. Chen–Liu–Liu–Wang, *Ordering and Inequalities for Mixtures
on Risk Aggregation*, Conjecture 1, accepted manuscript printed p25 (also arXiv
2007.12338v2), asserts D_n(F) ⊆ D_n(Λ ⊗ F) for every doubly stochastic Λ and
every tuple of decreasing-density marginals. Here inverse cdfs are mixed:
(Λ ⊗ F)^(-1) = Λ F^(-1). Decrease and inclusion are non-strict; density
monotonicity is on its support. We give a smaller explicit certificate for the
same n=2, full-average refutation, including weaker version (ii). No claim is
made about common-scale versions (i)/(iii).

Set q_k(0)=0 and make q_k affine on each interval [j/5,(j+1)/5], with slopes

| k | five successive slopes |
|---|---|
| 1 | 1, 13/10, 11/5, 14/5, 29/10 |
| 2 | 1/2, 9/10, 9/10, 8/5, 9/5 |

Let F_k be the law of q_k(U), U uniform on [0,1]. Both quantiles are continuous
and strictly increasing. On each image interval the density is the reciprocal
of its slope. The support endpoints are

    F1: 0, 1/5, 23/50, 9/10, 73/50, 51/25;
    F2: 0, 1/10, 7/25, 23/50, 39/50, 57/50.

Each image interval has mass (slope/5)/slope=1/5, so each density integrates
to one. All slopes are positive and nondecreasing: densities are positive and
nonincreasing on their interval supports. Breakpoint values may be assigned
the right-hand density; endpoint choices change no law. There are no atoms.
These reconstruct the literal source class, without approximation or smoothing.

Put r=(q1+q2)/2, and let G be the law of r(U). Its quantile on (0,1) is exactly r,
because r is continuous and strictly increasing. For the matrix with all four
entries 1/2, Λ ⊗ (F1,F2)=(G,G). Its support is [0,159/100].

## Four-piece continuous dual inequality

Write a=159/2000. Define H on [0,40] by affine interpolation of this table,
and extend it constantly beyond the endpoints:

| t | 0 | 4 | 10 | 20 | 24 | 38 | 40 |
|---|---|---|---|---|---|---|---|
| H(t) | 0 | -4 | 2 | -8 | -4 | -18 | -16 |

The payoff h(x)=a H(x/a) is precisely the original payoff with redundant knots
removed. It is continuous, bounded and 1-Lipschitz. Define

    D(t)=2-t+2(t-3)_+ -2(t-7)_+ +2(t-17)_+,  0≤t≤20,
    d(x)=a D(x/a),                              0≤x≤159/100.

The global inequality is

    H(s+t) ≤ D(s)+D(t)       for every s,t∈[0,20].                 (1)

Here is a finite analytic proof of (1), involving no discretization error.
The four affine intervals of D are I1=[0,3], I2=[3,7], I3=[7,17], I4=[17,20].
Their endpoint values are 2,-1,3,-7,-4. On each rectangle Ii×Ij cut along
s+t=k for k∈{4,10,20,24,38}. The slack D(s)+D(t)-H(s+t) is affine on every
resulting closed polygon. Its minimum is attained at a polygon vertex.
Every vertex is either a rectangle corner or the intersection of one of those
five lines with a rectangle edge. Symmetry reduces this to ten rectangles.
Exact substitution gives:

| (i,j) | 11 | 12 | 13 | 14 | 22 | 23 | 24 | 33 | 34 | 44 |
|---|---|---|---|---|---|---|---|---|---|---|
| distinct vertices in rectangle | 6 | 6 | 5 | 4 | 4 | 5 | 5 | 6 | 4 | 6 |
| minimum slack at these vertices | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

This is 51 exact vertex substitutions (some points recur across rectangles).
The vertex-generation rule and rational formulas fully specify every check;
`check_exact.py` independently implements them with Fraction arithmetic and
no optimization or imported discovery code. Thus (1) holds throughout the
square, including boundaries, not merely at sampled quantiles.

For every pair of random variables Z,W with marginals G, (1) implies

    E h(Z+W) ≤ E[d(Z)+d(W)] = 2∫_0^1 d(r(u)) du
             = -83231059/641080000 =: B.                        (2)

All quantities are bounded. No independence or inverse-uniform representation
of the joint law is needed. To check the integral, split [0,1] at

    0, 1/5, 617/2200, 2/5, 1613/3100, 3/5, 4/5, 4223/4700, 1.

The three non-fifth interior points solve r(u)/a=3,7,17 respectively.
On each resulting interval d(r(u)) is affine, so the trapezoidal formula is
exact. This proves the global target bound with zero rounding allowance.

## Twenty-interval source coupling and exact integration

On [i/20,(i+1)/20), i=0,...,19, set V=U+(p_i-i)/20, with

    p=(17,16,15,14,13,11,10,9,7,5,3,1,0,18,19,12,8,6,4,2).

This list is a permutation of 0,...,19. Translation carries each source interval
onto the corresponding target interval, so V is uniform. Hence the law J of
q1(U)+q2(V) lies in D2(F1,F2).

For completeness these are the exact integrals of h(q1(u)+q2(u+(p_i-i)/20))
over the twenty successive intervals (not conditional averages):

    7/10000, 27/10000, 89/20000, 2969/520000, 6997/1160000,
    99/20000, 2573/440000, 2813/440000, 7253/1240000, 7453/1240000,
    6461/1080000, 143/40000, -57/40000, -21/800, -151/4000,
    -5149/275000, -37387/1900000, -69769/3800000,
    -35407/1900000, -11/500.

These are derived as follows, providing reproducible analytic integration rather
than a numerical objective. For each interval first split at u=j/5 and
u=j/5-(p_i-i)/20 that lie inside it. On any such piece f(u)=q1(u)+q2(V(u))
is increasing affine. Insert its unique preimage of each payoff breakpoint
ak, k∈{4,10,20,24,38}, that lies strictly inside the piece. The total is 31
affine subpieces. Each integral is exactly
(right-left)(h(f(left))+h(f(right)))/2. Summing gives

    A=E_J h=-68997954679/659497410000.
    A-B=100817889097/3999532680000 > 0.                          (3)

By (2)-(3), J cannot be the law of any sum with both marginals G. Therefore
D2(F1,F2) is not contained in D2(G,G), at exactly the original source scope.

## Limits

This proof compresses 200 source bins and 200 discrete dual entries/40000
inequalities plus error allowances into 20 bins, four continuous dual pieces,
51 vertex substitutions and exact integrals. Neither witness minimality nor
optimality of the coupling/dual/gap is claimed. The smaller coupling was found
using a bounded finite assignment calculation, but its delivered proof uses only
the displayed permutation and rational inequalities. The checker is an independent
implementation within this solo lane, not an independent human/agent review or
kernel-checked proof. All original novelty/source/registry holds remain unchanged.
