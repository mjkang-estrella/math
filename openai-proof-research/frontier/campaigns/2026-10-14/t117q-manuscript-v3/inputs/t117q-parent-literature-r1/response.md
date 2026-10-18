# T117Q: response to contribution review RQ1–RQ4

Myeongjin Kang, no affiliation. Original prose CC BY4.0; code MIT.
Parent author response, not an independent contribution or acceptance verdict.
The frozen theorem and candidate are unchanged. Author manifest:
`053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2`.
Contribution review manifest:
`6d6366df9904a9d49db95e218c1daf52b444878ee2ec9ecf6938f9b84dfb5013`.

## RQ1: additional comparisons

Naor–Pisier–Schechtman, arXiv:1710.08896, discuss the obstruction to
transferring coordinate sampling to trace class and dimension-dependent
geometry of its finite-dimensional subspaces. Their results concern
dimension reduction and already embedded subsets; they do not give this
all-target-dimensions obstruction for a negative-type source family.
Naor–Young, arXiv:1701.00620, Question13 and its discussion concern
Heisenberg groups and trace-class nonembedding. T117Q constructs a different
family and proves no statement about those groups. Both are close context,
not priority evidence or problems solved by T117Q.

Cordero-Erausquin–Eskenazis, arXiv:2010.11583, Theorem13, and
Luo–Wang–Zhou, arXiv:2610.03407, Theorem1.1, do supply a real alternative
functional-inequality route for cube quotients. There is a useful
qualification to the round1 comparison: although Theorem13 is stated as a
bi-Lipschitz lower bound, its proof (123), before (124), is already a
pair-average inequality. For a nonexpanding quotient map F, (125) bounds
each coordinate increment by one half of the boundary indicator. Thus
one obtains an average upper bound controlled by geometric influences,
under the pushforward of uniform cube measure. It would be inaccurate to
dismiss this route solely because the displayed theorem says bi-Lipschitz.

What the operative statements do not provide is a family of genuine
negative-type quotient metrics with the requisite influence estimates and
pair-average scale giving T117Q's rate, followed by uniformization if class
sizes differ. The source117 multichart construction is not identified with
such a quotient. T117Q instead proves its trace-norm contraction directly
by spectral projections and a positive trace pairing. This is a comparison
of supplied hypotheses and operations, not an impossibility theorem about
all future uses of Talagrand type. Independent round2 should specifically
check this qualification and any reduction the author has missed.

## RQ3: sharp metric cotype and its grid consequence

Jiao–Luo–Wu, *The Sharp Scale Inequality for the Schatten Trace Class*,
arXiv:2610.21445v1, was posted15October2026. The actual primary abstract and
the paper's Theorem1.3 were checked. It proves the squared-distance torus
cotype inequality with constant `3 sqrt(70) m + 6 sqrt(d)`, so the scale
`m` can be of order `sqrt(d)`. We fully credit this antecedent. Its
introduction also constructs a nonlinear matrix smoothing map with an
ell2 sum of coordinate derivative norms; the present proof does not claim
that dimension-free trace-class smoothing is unavailable.

Giladi–Mendel–Naor, arXiv:1003.0279v3, §1.3 and Question3, and
Mendel–Naor, arXiv:math/0506201, proof of Theorem1.12, explain the grid
distortion consequence. The latter inserts a co-Lipschitz lower bound for
every long coordinate jump into cotype. Sharp scaling therefore pays the
large bi-Lipschitz distortion of the usual sup-norm grids. That alone does
not pay T117Q, for two explicit reasons.

First, these grids have uniformly bounded first average distortion into
the real line, hence into S1. For `G={0,...,k}^d`, `k>=1`, choose any
rank-one orthogonal projection P and set `F(x)=x_1 P`. This is1-Lipschitz
for the sup metric. For independent uniform U,V in `{0,...,k}`,

    E|U-V| = [2/(k+1)^2] sum_{h=1}^k h(k+1-h)
           = k(k+2)/(3(k+1)) >= k/3.

Meanwhile `E d_infinity(x,y) <= k`. Thus this particular map preserves
at least one third of the uniform pair-average distance, in all d and k.
The grid lower bound for bi-Lipschitz distortion cannot be substituted for
a diverging lower bound on uniform first average distortion. This exact
argument is stronger than an analogy with commutative L1.

Second, the usual grids are not negative type once d>=3 and k>=2. In the
three-dimensional side2 grid take positive-weight points

    A={(2,1,0),(0,1,0),(0,1,1)}

and negative-weight points

    B={(1,0,1),(1,0,0),(1,2,0)},

with weights +1 on A and −1 on B. The weights sum to0. The unordered
within-A and within-B distance sums both equal5, and all9 cross-distances
equal1. Hence `sum_{i,j} c_i c_j d_infinity(x_i,x_j)=2*5+2*5−2*9=2>0`.
This contradicts the necessary conditional-negative-definiteness identity
for squared Hilbert distances, whose left side would equal
`−2 ||sum_i c_i v_i||^2`. The same subset embeds in every larger such grid.

These arguments rule out the standard grid substitution, not every
conceivable use of metric cotype. The cotype inequality compares selected
long torus jumps with local random jumps in second moment. T117Q concerns
all uniform pairs in first moment on a separate negative-type family.
No reduction connecting those inputs is supplied by the read statements.
The nonlinear mixing smoother in Jiao–Luo–Wu also does not state the
simultaneous multichart coefficient/positive-selector estimate of T117Q;
using it here would require a new compatibility argument. The parent has
not audited the complete mixing proof or claimed such an argument impossible.

## RQ2 and RQ4: exact claim language

The result is new to this project, with no antecedent found in a bounded
search. Literature priority is not demonstrated. No claim of “first”, of
solving the Heisenberg question, or of settling Escudero Gutiérrez–Muguruza
Question2 will appear. The exponent9/2 and the number of charts were
selected by the method before the scope freeze; the freeze preceded the
complete proof, not the method. Through the diagonal inclusion of ell1
into S1, the theorem gives an ell1 bound with denominator exponent9/2,
weaker than source117's exponent3. It does not supersede that source bound.

The manuscript must implement all these comparisons and qualifications.
This addendum neither changes frozen files nor creates an accepted result.

## Actual reading limits

Parent read the complete contribution report and reading ledger. Primary
reads in this followup: Jiao–Luo–Wu local lines1–282 (introduction, exact
Theorem1.3, smoothing overview, beginning of matrix preliminaries);
Giladi–Mendel–Naor lines55–160 and377–505 (definition/main bound and full
§1.3); Mendel–Naor lines3010–3060 (grid argument, not full cotype proof);
Naor–Pisier–Schechtman lines280–339; Naor–Young lines590–634;
Cordero-Erausquin–Eskenazis lines466–555 and1940–2015 (Theorem13 and proof);
Luo–Wang–Zhou Theorem1.1 and surrounding introduction (display of1–165 had
a short unrelated introductory paragraph elided; no full proof read).
Earlier oversized combined output was truncated; the operative GMN
passages were subsequently reread in bounded displays. The grid average
and six-point certificate above are parent derivations, not attributed to
the papers. New PDF/text identities are in retrieval.json; review-cache
copies retain provenance. No full bibliographic/forward-citation search.
