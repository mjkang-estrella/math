# Conditional half-plane transfer for the circuit cap

Parent author derivation, 2026-10-18. This is a live supporting lemma, not a
full no-bigeodesics proof, independent review, or nomination. It uses the
cap construction and coding tails in fresh-analytic-discovery-r74. The
all-ray structure hypotheses below remain obligations of that investigation.

## Scope and antecedent

I read all 596 lines of the pinned source212 file
`No-bigeodesics-in-planar-first-passage-percolation-September-24-2026/build/sections/04-exceptional.tex`.
Its cut-transfer lemma uses exact shared edge weights above/below a horizontal
cut. Its last-cut barrier, calibration-defect limit, and two-direction
Busemann identification are the antecedents for the argument here. What
changes is the cut: capped fields need not coincide on either exact half-plane.
The replacement below uses their actual changed-edge endpoints and proves
the geometric estimates that this replacement needs. No new primary-body
reading is claimed in this note.

Let X=(t,U) be the iid original field and independent auxiliary uniforms,
and let s=Phi(X) be the circuit cap. For each edge e, L_e is the length of
a shortest M-open simple circuit strictly surrounding both endpoints, and
s_e=min(t_e,M(L_e^3+U_e)). The same argument works for any cap with this
finite local determination; no moment claim about the original t is used.

Assume the following properties of the cap law have been established on a
single full-measure event:

1. Every L_e is finite, and L_e=o(|e|) uniformly over distant edges. Here |e|
   is the Euclidean norm of its midpoint. The stretched-exponential bound
   in the author notes supplies this by summability over lattice edges.
2. Finite geodesics exist uniquely. The common deterministic norm m satisfies
   |T(x,y)-m(y-x)|=o(|x|+|y|) uniformly as |x|+|y| tends to infinity.
3. Every ray p has a Busemann function B_p, with
   B_p(0,w)=rho_p(w)+o(|w|), and all its limit directions are contacts of
   rho_p with m. Busemann increments satisfy the metric bound and calibration
   on p. These properties hold simultaneously over rays.

Fix a chart whose upper labels have all contact directions strictly above
the horizontal axis, and whose lower labels have contacts strictly below it.
As in the source, the angular gap can depend on the particular label; no
uniformity over labels is asserted.

## Splice the underlying field, then cap it

Use the source edge partition E_n^+ (both endpoint heights at least -n).
Form X_n^V from X above the cut and an independent replacement field below;
form X_n^W from another independent replacement above and X below. Splice
both t and its auxiliary U. For each fixed n, X_n^V and X_n^W are independent
with the same law as X. Consequently their capped images V_n and W_n are
independent with the cap law. This independence is not asserted across n.

Let D_n^V be all endpoints of edges where Phi(X) differs from Phi(X_n^V).
Define D_n^W similarly. These are actual changed-vertex sets, possibly
infinite; no connectedness or curve representation is needed.

If an edge e above the physical cut has the same original weight and auxiliary
in both fields, and a shortest protecting circuit in each field stays entirely
in the shared edge region, each circuit is admissible in the other field.
Their lengths, and therefore their capped weights at e, coincide. Every point
of a protecting circuit is within L_e+2 of either endpoint of e. Thus a changed
edge above the cut must have, in at least one of the two fields, a protecting
circuit long enough to reach the cut. The additive constant 2 absorbs endpoint
and midpoint conventions. It follows, with a harmless enlargement of constants,
that every z in D_n^V satisfies

    z_2 <= -n + 3 + max_{e incident to z}(L_e(X)+L_e(X_n^V)).       (1)

Edges originally replaced below the cut satisfy the same bound directly.
For D_n^W the reflected bound is

    z_2 >= -n - 3 - max_{e incident to z}(L_e(X)+L_e(X_n^W)).       (2)

Only the existence of some minimum circuit in each field is needed; choosing
them equivariantly or selecting equal representatives in ties is unnecessary.

## One deterministic subsequence for all upper witnesses

Define

    A_n(X)=sup_e L_e(X)/(|e|+n),
    E_n(T)=sup_{x,y}|T(x,y)-m(y-x)|/(|x|+|y|+n).

The first and second assumptions imply A_n(X)->0 and E_n(T)->0 almost surely:
the uniformly sublinear tail contributes arbitrarily little, and finitely
many remaining entries are divided by n. Since X_n^V has the same marginal
law as X, A_n(X_n^V) and E_n(T_{V_n}) tend to zero in probability. Choose a
deterministic increasing n_k so that

    P(max(A_{n_k}(X_n^V),E_{n_k}(T_{V_{n_k}}))>2^-k)<2^-k.

Borel--Cantelli, together with the almost-sure original-field limits, now
gives a single sequence on which all four errors vanish. Equation (1) implies
there are random epsilon_k->0 such that

    z in D_{n_k}^V => z_2 <= -n_k + epsilon_k(|z|+n_k).             (3)

The constants 3 and midpoint shifts are absorbed since n_k tends to infinity.
For every fixed n, the ordinary sublinearity of L in both marginals also gives

    z in D_n^V => z_2 <= o(|z|)+O_n(1),
    z in D_n^W => z_2 >= -o(|z|)-O_n(1).                          (4)

These statements mean that for every delta>0 each inequality has a finite
constant C_{n,delta}, uniformly over z. They hold simultaneously for all n.

## Moving barrier for bounded basepoints

Fix an upper ray p and its label rho. Write
a(w)=B_p(0,w)-rho(w)=o(|w|). Compactness gives a positive gap on the closed
lower semicircle. By continuity there exist eta>0 and gamma>0 such that

    m(d)-rho(d) >= gamma |d| whenever d_2 <= eta |d|.             (5)

Let K be finite, containing p_0, and bound |x| by R for x in K. For large k,
(3) implies |z|>=n_k/2 for every z in D_{n_k}^V. Uniformly over such z and x,
|z-x|>=|z|/2 and |x|+|z|+n_k<=8|z-x|. Also

    (z-x)_2 <= 3 epsilon_k |z| + R,

so its ratio to |z-x| is at most eta for all sufficiently large k. The moving
metric error and the two Busemann errors therefore give, in BOTH metrics,

    min(T_U(x,z),T_{V_{n_k}}(x,z))-B_p^U(x,z)
       >= (gamma/2)|z-x| >= gamma n_k/8,                         (6)

after increasing k. The last constant may be weakened without effect. Here
U denotes the original capped metric, not the auxiliary uniform variable.
The error estimates are uniform over the infinite changed-vertex set.

The entire ray p avoids D_{n_k}^V for large k. Indeed its contact directions
are in a strict upper sector, so p_j,2>=c|p_j| eventually for some c>0.
Equation (3), with epsilon_k<c/2, excludes every sufficiently far ray vertex;
the remaining finite prefix is excluded by taking n_k large. In particular
all edge weights on p are shared.

For a finite walk from x to p_j meeting D_{n_k}^V, let z be its LAST vertex
in that set. Its suffix from z has no changed edge: a changed edge would have
both endpoints in D and give a later such vertex. Hence its cost in V is at
least B_p^U(z,p_j), while its prefix costs at least T_V(x,z). Its total cost
is therefore at least B_p^U(x,p_j)+gamma n_k/8. The identical argument holds
in U. Walks avoiding D have exactly the same costs in both fields.

Taking x=p_0 preserves every prefix of p as a geodesic in V. For x in K,
the usual calibration defect T_U(x,p_j)-B_p^U(x,p_j) tends to zero. Once it
is below gamma n_k/8, a minimizing U path avoids D and is a shared competitor;
the V barrier excludes every changed competitor. Thus

    T_V(x,p_j)=T_U(x,p_j) for all sufficiently large j, x in K.   (7)

This preserves every requested finite Busemann witness. For finitely many
upper rays one takes the maximum of their finitely many thresholds. No
subsequence depending on those rays was used.

## Fixed-cut barrier and exact labels

Fix n, the two environments, and an upper ray already preserved. Fix c>0 and
consider x_2>=c|x|. Equation (4) says that for every delta>0,
z_2<=delta|z|+C_delta on D_n^V. Choose delta<=c/8. For sufficiently large |x|,
if |z-x|<c|x|/4, then |z|<2|x| and
x_2-z_2 >= (c-2delta)|x|-C_delta > c|x|/2,
a contradiction. Consequently, with kappa=c/(c+8),

    |z-x| >= kappa(|x|+|z|)                                    (8)

uniformly over z in D. Decrease delta further so that delta/kappa<eta/2.
Since (z-x)_2<=delta|z|+C_delta, (8) puts this displacement in the enlarged
lower cone (5) for all sufficiently large |x|. The uniform fixed-metric
estimate and the two Busemann errors, each bounded by arbitrarily small
multiples of |x|+|z| plus a constant, give

    min(T_U(x,z),T_V(x,z))-B_p^U(x,z)
       >= (gamma kappa/4)(|x|+|z|)                              (9)

for all sufficiently far x in the sector and all z in D. Such x themselves
are outside D. The preserved p is outside D as well. The last-changed-vertex
argument and calibration defect now give eventual equality of distances
from x to p_j. Distances from the anchor p_0 already agree for every j, so
the Busemann functions agree on (p_0,x) throughout this far upper sector.
Use x=k e_2 and x=k(e_1+e_2), with c=1/2. Their two independent directions
identify the Busemann linear functional in V as exactly rho.

For each fixed W_n, apply the reflected version of (8)--(9) to D_n^W and
any lower U-ray q. A sufficiently late tail of q is disjoint from D_n^W;
choose its starting vertex far enough that the reflected barrier applies.
The same last-changed-vertex comparison preserves that entire tail. Compare
distances at far x in a strict lower sector, using -k e_2 and -k(e_1+e_2),
to identify its label exactly. Thresholds may depend on n and q. The initial
common event includes all W_n, so this holds pathwise for every lower ray
and every fixed n without a new uniformity assertion over labels.

## Conditional consequence and remaining limits

Subject to hypotheses 1--3, this proves both quantifiers of source212's
cut-transfer lemma for the capped fields, including exact finite Busemann
witnesses and exact opposite labels. Independence is supplied by the
underlying splice, not by independence of capped edge weights. If the all-ray
structure and fixed-label coalescence theorem are completed, the source's
countability and analytic-set/Fubini proof then gives opposite coalescence
at every exceptional cap label by the same four-witness argument.

This does not prove those structural premises, restore cap finite energy,
or transfer the later fork/tilt arguments. It is an author-level deduction
requiring separate scrutiny before a full candidate can be frozen. No
finite check is offered as a substitute for these pathwise arguments, and
the accepted count remains 16/20.
