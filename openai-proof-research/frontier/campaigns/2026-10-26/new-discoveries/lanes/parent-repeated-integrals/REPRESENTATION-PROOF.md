# Concrete representation assembly, with two remaining premises

This supplements the unchanged preliminary-review freeze. It is not final
acceptance and contributes no discovery credit. The original source definitions
and MomentDefs interface remain unchanged.

The new formal route avoids constructing the whole closed moment cone. Write
A = smoothMomentSet n and p(t) = (1,t,...,t^n). The endpoint map T is proved to
be a continuous linear equivalence. Before reversing its output coordinates,
its matrix is lower triangular, with entry choose(r,i)(-1)^i/r! and diagonal
(-1)^r/r!. The binomial theorem and finite integral interchange establish
T(moment(rho))_j = integral (1-t)^(n-j)rho(t)dt/(n-j)! literally.

Repeated primitives of rho give a global smooth function F. Lean proves every
initial derivative through n is zero, every terminal derivative equals T's
corresponding coordinate, F^(n+1)=rho, and every higher endpoint derivative is
zero whenever rho equals one near both endpoints. The resulting data belongs
to the original SourceW n, using strict monotonicity of F^(n).

For the other inclusion, SourceMeasure constructs from each original source
witness a finite nonzero atomless measure mu supported on [0,1]. Its exact
endpoint formulas imply T(moment(mu))=b. These formulas are established by
within-derivative Taylor remainder and a genuine Fubini interchange; no extra
derivative of the original continuous monotone highest derivative is assumed.

The representation theorem currently takes only the concrete statements
Convex R A and IsOpen A as premises. Assume its conclusion fails. Separation
then supplies a continuous linear functional L with L(z)<L(moment(mu)) for
every z in A.

First, zero is in closure A. For 0<delta<1, put

  beta = delta + (1-delta)(chi_0+chi_1),

where each smooth cutoff equals one near its endpoint and has outer radius
delta. The opposite cutoff vanishes near that endpoint. Thus beta is a good
density. Its mass is at most 5delta, and every moment is between zero and
5delta. Letting delta approach zero proves the closure statement. Separation
and continuity therefore imply 0 <= L(moment(mu)).

Second, L(p(t))<=0 on [0,1]. If it were positive at an interior point, a smooth
nonnegative bump psi supported inside the region of positivity would satisfy
integral L(p(t))psi(t)dt>0. Every density 1+c psi with c>=0 belongs to A.
Taking c sufficiently large contradicts L's upper bound on A. Continuity
extends the nonpositivity to both endpoints. The formal proof constructs the
bump and proves positivity of its actual integral, rather than assuming an
approximation or existence certificate.

Finally L is nonzero, since a strict separating functional cannot vanish on
the nonempty A. Its coefficient polynomial q(t)=-L(p(t)) is therefore nonzero
and nonnegative on [0,1]. Its zero set is finite. Atomlessness, positive mass,+and integrability imply integral q dmu>0, hence L(moment(mu))<0, a
contradiction. This proves moment(mu) belongs to A.

Consequently SourceW n = T '' A, and the all-order source conjecture follows
from convexity/openness of the actual A. SourceAssembly.lean records this
composition with those two explicit premises. They must be discharged by the
parallel implementation before a closed source theorem, paper, final review,
or discovery credit is claimed. No known general moment-cone fact is counted
as a separate outcome.
