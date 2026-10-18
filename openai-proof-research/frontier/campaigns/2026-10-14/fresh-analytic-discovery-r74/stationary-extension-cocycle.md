# Uniform linearity on a stationary extension without assuming ergodicity

Author derivation prompted by the explicit warning in the elementary cap
assistance and the parent's proposed repair. This is a supporting bridge for
AH9.2 and other increment extensions, not an independent gate. It uses the
already proved cap marginal shape and local continuity. The extension itself
need not be ergodic under any translation.

Let an arbitrary translation-invariant probability law carry the cap metric T
and a real additive, translation-covariant cocycle B(x,y) satisfying
|B(x,y)|<=T(x,y). Its metric marginal is the cap law. The law of the other
coordinates can have invariant randomness. All statements below hold on one
full event in this extension. Finite cap moments imply integrable B(0,e_i).

## Axis limits and global invariance

By the two-sided Birkhoff theorem for translation by e_i, for i=1,2,

 B(0,k e_i)/k -> rho_i as k->plus or minus infinity.

The two signs have the same limit (the conditional mean on that translation's
invariant sigma-field). No deterministic value is asserted. Include countably
many shifted roots in this event. For each fixed w in Z², additivity gives

 |B(w,w+n e_i)-B(0,n e_i)|
 <= T(0,w)+T(n e_i,n e_i+w).

The second term has the fixed distribution T(0,w), which has a finite first
moment. Thus for every eps>0,

 sum_{n>=1}P(T(n e_i,n e_i+w)>eps n)
 =sum_{n>=1}P(T(0,w)>eps n)<infinity.

Borel–Cantelli, with no independence requirement, makes the displayed
difference divided by n tend to zero. Countably many w and rational eps give
rho_i(theta_w omega)=rho_i(omega) for every w. Hence the vector rho is
invariant under the FULL translation group, not just its own axis. Ordinary
cap shape and |B|<=T also give |rho_i|<=mu(e_i); in particular rho is uniformly
bounded by a deterministic constant. This avoids assuming that cap mixing
lifts to the enlarged probability space.

## Fixed good-center events on nonergodic components

Fix alpha>0. For integer N define Q_N(v) by BOTH axis bounds

 |B(v,v+k e_i)-k rho_i|<=alpha |k|,
 i=1,2, all integer |k|>=N.

By the axis convergence Q_N(0) increases to a probability-one event.
Because rho is globally invariant, Q_N(v) is the translation of Q_N(0).
Let I be the full group-invariant sigma-field. Conditional monotone
convergence yields

 d_N=E[1_{Q_N(0)^c}|I] decreases to zero a.s.

For every deterministic N the spatial ergodic theorem gives bad-center
density d_N in expanding centered squares, even on this nonergodic law.
Take their countable intersection. For any eta>0 and each realization there
is a FINITE integer N with d_N<c eta². This N may depend on its invariant
component. That causes no varying-event ergodic step: all deterministic N's
spatial limits already hold simultaneously before choosing one. With c a
sufficiently small absolute constant, eventually there are fewer than half
the lattice-point count of Q_{eta R} bad centers in Q_{3R}, even after doubling
for two tests below.

For ANY x in Q_R, choose v in Q_{eta R} such that v and v+x_2 e_2 are both
good centers. Such a choice exists uniformly in x: failures of the first
condition number at most the bad count in Q_{3R}; failures of the second
condition are in bijection with bad centers after translation by x_2 e_2,
again within Q_{3R}. Their union is smaller than the candidate square. The
choice is only a deterministic existence argument; no measurable selector
of v is required for the resulting uniform inequality.

## Uniform radial conclusion

Use the cocycle route

 0 -> v -> v+x_2 e_2 -> v+x -> x.

For the two middle axis segments with |x_i|>=N, the combined difference
from rho_2 x_2+rho_1 x_1 is at most alpha(|x_1|+|x_2|)<=2alpha R.
If an axis segment has |x_i|<N, domination by T and uniform local metric
continuity instead bounds its error by C(N+zeta R)+C_mu N, for any fixed
small zeta>0 and all sufficiently large R. This bound is uniform in the
chosen start inside Q_{3R}. The first and last segments have displacement v;
their absolute B-values are at most C(eta+zeta)R by local continuity.
Combining the four segments gives

 sup_{x in Q_R}|B(0,x)-rho·x|/R
 <= C'(eta+zeta)+2alpha+O(N/R)

for all sufficiently large R. Choose eta,zeta,alpha small in that order as
needed and then R large; take a countable sequence of target errors. Therefore

 sup_{x in Q_R}|B(0,x)-rho·x|/R ->0 a.s.

In particular B(0,x)-rho·x=o(|x|) uniformly at infinity, by taking R=|x|_infty.
Additivity immediately gives the extended bound

 |B(x,y)-rho·(y-x)|<=eps(|x|+|y|)+C_eps

for all x,y, with random finite C_eps. Thus the random invariant functional
has exactly the uniform linearity needed in the AH9.2 extension argument.
Its remaining supporting-arc and deterministic selector-direction deductions
are the actual-read AH9.2 proof using these bounds and cap shape. This lemma
does not claim that rho is deterministic on the extension, that its graph
is a measurable function of the cap field, or that its paths coalesce.
