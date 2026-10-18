# Uniform cocycle linearity on a possibly nonergodic extension

Parent author lemma, 2026-10-18. This closes an explicit probability interface
in the live r74 structural construction. It does not establish that the needed
limiting cocycle/path extension exists, nor does it certify the full theorem.
The underlying cap field being mixing does not imply that its extension is
ergodic, even under one coordinate shift. No such implication is used here.

## Hypotheses and conclusion

Let a probability space carry a measure-preserving Z² action, a stationary
random metric T on Z², and a stationary additive real cocycle B(x,y). Suppose:

* |B(x,y)|<=T(x,y) for all lattice x,y, with E T(0,z)<infinity for each fixed z;
* for every eta>0, almost surely eventually for all x,y in Q_R=[-R,R]²,
  T(x,y)<=C(|x-y|_1+eta R), with a deterministic finite C independent of eta;
* T(0,n e_i)/n converges to a deterministic finite mu(e_i), for i=1,2.

These are properties already proved for the cap marginal and inherited by
any extension having that marginal. Then there is a measurable, translation-
invariant random linear functional rho such that

    sup_{x in Q_R}|B(0,x)-rho(x)|/R -> 0 almost surely.           (1)

In particular rho need not be deterministic. The random functional is bounded
by deterministic constants on the coordinate vectors. Additivity then gives

    sup_{x,y in Q_R}|B(x,y)-rho(y-x)|/R -> 0.                   (2)

The only general probability inputs are ordinary one-parameter Birkhoff and
the spatial ergodic theorem for the Z² action, each with its invariant
sigma-field rather than a presumed trivial invariant sigma-field.

## Axis limits are invariant under the whole action

By additivity,

    B(0,n e_i)=sum_{k=0}^{n-1} B(k e_i,(k+1)e_i).

The summands form a stationary integrable process. Birkhoff gives a finite
axis limit rho_i, initially invariant only under translation by e_i. The
backward average for the same invertible transformation has the same
conditional expectation on that invariant sigma-field. Hence

    B(0,k e_i)/k -> rho_i as |k|->infinity, k in Z.

For any fixed w, the cocycle identity gives

    |B(w,w+n e_i)-B(0,n e_i)|
       <= T(0,w)+T(n e_i,n e_i+w).                            (3)

The last variables have the common marginal law T(0,w). Its finite first
moment implies sum_n P(T(n e_i,n e_i+w)>epsilon n)<infinity, for every
epsilon>0: this follows from the usual tail-sum bound for an integrable
nonnegative variable, without independence. Borel--Cantelli shows that (3),
divided by n, tends to zero. Stationarity identifies the limit on the shifted
sample with rho_i translated by w. Thus rho_i is invariant under every w.
Take a countable intersection over i,w and rational epsilon.

The metric bound and deterministic radial limits give |rho_i|<=mu(e_i).
Define rho(x)=rho_1 x_1+rho_2 x_2. This is a globally invariant random linear
functional with a deterministic norm bound. What remains is uniformity away
from the two axes; it does not follow from Birkhoff alone.

## Good centers on a nonergodic space

Fix rational delta>0. For deterministic N define G_N(v) to be the event that
for both i and every integer k with |k|>=N,

    |B(v,v+k e_i)-k rho_i|<=delta |k|.

By the axis limits, G_N(0) increases to a full-measure event. Because rho is
invariant under the entire action, G_N(v) is exactly the translate of G_N(0).
Let I be the invariant sigma-field of the full Z² action. Conditional monotone
convergence gives

    E[1_{G_N(0)^c} | I] -> 0 almost surely.                    (4)

The spatial ergodic theorem, applied to each fixed N, says that the asymptotic
frequency of bad centers is this conditional expectation. Countability lets
these conclusions hold together for every N and rational delta. For any fixed
rational eta in (0,1), on each such sample choose SOME integer N for which the
conditional expectation in (4) is below eta²/10000. This N may depend on the
invariant component; it is not inserted into an ergodic theorem for a moving
event. Every deterministic N was already included in the common full event.

For all sufficiently large R, fewer than eta² R²/100 bad centers lie in Q_{3R}
(enlarging the numerical denominator in (4) if needed for box normalization).
For each x=(x_1,x_2) in Q_R, consider all integer v in Q_{eta R}. Both v and
v+x_2 e_2 are in Q_{3R}. The number of choices failing either goodness test is
at most twice the total number of bad centers there, since translation by
x_2 e_2 is injective. The candidate set has asymptotic size4 eta² R².
Therefore, simultaneously for EVERY x in Q_R, there is a v in Q_{eta R}
such that both v and v+x_2 e_2 are good. No rate or independence of good
centers is required, and their selection need not be measurable for this
pathwise estimate.

## A two-axis route proves the uniform conclusion

Use the cocycle route

    0 -> v -> v+x_2 e_2 -> v+x -> x.

The middle two increments start at the two good centers. If |x_i|>=N their
errors relative to x_i rho_i are at most delta |x_i|. If |x_i|<N instead use
the local metric bound, in a fixed enlargement of Q_R and with remainder
eta R, to bound the increment by C'(N+eta R). The corresponding linear term
is at most a deterministic constant times N. The two end corrections have
total error at most C'' eta R relative to their linear terms, because |v| is
O(eta R), |B|<=T, rho is deterministically bounded, and local metric continuity
holds uniformly. All four linear terms sum to rho(x).

Thus, for all sufficiently large R, uniformly over x in Q_R,

    |B(0,x)-rho(x)| <= C_1 eta R + 2 delta R + C_2 N.           (5)

Constants do not depend on eta,delta,N,R or x (apart from the deterministic
metric/radial constants). For fixed eta,delta, N is finite on the sample, so
its contribution vanishes after division by R. Let eta and delta decrease
through rational sequences on the already chosen common event. Equation (1)
follows. Finally B(x,y)=B(0,y)-B(0,x) gives (2).

If a ray in this extension is B-calibrated, the metric norm and (1) identify
each of its limiting directions as a contact direction of rho. That further
consequence requires calibration and the deterministic cap shape; the lemma
does not manufacture either premise. It also makes no assertion about the
heavy-tailed original metric or its Busemann functions.
