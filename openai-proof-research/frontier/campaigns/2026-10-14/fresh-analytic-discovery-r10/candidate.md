# Everywhere-positive Coulomb marginals: research r10

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party inputs remain private and retain their rights.

**UNRESOLVED.** The frozen target P is neither proved nor refuted. No result
is nominated, no independent gate has run, and the campaign remains **4/10**.
The global dual extension below is a supporting deduction, not a substitute
for P. There is no manuscript, Lean, publication or submission claim.

## 1. Exact frozen problem

Find a real Schwartz function g on R^3 with g(x)>0 for every x and
integral g^2=1. Put rho=g^2 and mu=rho dx. For

    c(x,y,z)=1/|x-y|+1/|x-z|+1/|y-z|,
    E(mu)=inf_{pi in Pi(mu,mu,mu)} integral c dpi,

with infinite cost at a collision, the requested conclusion is:

* E(mu) is finite and attained by a coupling;
* for **every** preserving Borel pair T2,T3,

      integral c(x,T2(x),T3(x)) dmu(x) > E(mu);

* the infimum over these pairs equals E(mu), and finite-cost pairs approach it.

The inequality allows an infinite left side. Maps need not be continuous,
cyclic, Sobolev or of bounded complexity. The missing conclusion is exclusion
of **every** deterministic optimizer for one everywhere-positive smooth
square density. No density with gaps, approximate marginal, altered cost,
or exhibited non-Monge optimizer replaces it. The exact scope was frozen
in `original-scope.md`, before the sustained proof attempt; its hash is in
`scope-freeze.json`.

The finiteness, direct-method existence, and equality of infima are paid
operations. Indeed any bounded probability density rho satisfies

    integral |x-y|^-1 rho(y)dy <= 2 pi ||rho||_infinity+1.

Split at |x-y|=1 and integrate the kernel over the unit ball. The product
coupling therefore has finite cost. Couplings with fixed marginals are
uniformly tight: mu(K)>1-epsilon/3 gives pi(K^3)>1-epsilon. A weak limit
retains the three marginals, and the nonnegative lower semicontinuous cost
gives attainment by the direct method. Colombo--Di Marino's actual
Theorem 1.1 (2013 author version), with Remark 1.3, gives equality of the
Coulomb infima for nonatomic marginals, even with cyclic approximating
maps. It does not give attainment by maps. These facts do not prove P.

## 2. Stipulated input and why this is a different operation

All OpenAI contracts below are stipulated true at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source is family 373,
*A counterexample to the Monge ansatz for the three-marginal Coulomb cost*.
Its exact pinned prefix is

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/build/

The actual interfaces read are `sections/introduction.tex`, `thm:main`;
`sections/local.tex`, `lem:local`; `sections/certificate.tex`,
`prop:certificate` and `lem:common-ball`; `sections/splitting.tex`,
`lem:splitting`; and `sections/proof.tex`. They supply:

* A ball B about 0, four smooth diffeomorphisms H_j onto disjoint open
  images, and the bounded open union V=B union_j H_j(B).
* A bounded componentwise smooth u on V with sum_i u(x_i)<=c on V^3.
  Every contact with first coordinate x in B has its other coordinates
  equal to one prescribed opposite pair H_j(x), in either order.
* Every x in B has both prescribed contact triples. Consequently every
  point of V is a coordinate of an old contact triple.
* The five center values are u(0)=5/2 and u(plus/minus e_k)=0 for k=1,2.
* For any nonnegative g_b in C_c^infinity(B), integral g_b^2=1, put

      nu=g_b^2 dx,
      mu_0=nu/3 + sum_j (H_j)#nu/6.

  A symmetric finite optimal plan pi_0 is supported on those contacts.
  The marginal has a smooth compactly supported square root.

All these properties follow from the named statements, not catalogue
summaries. `sections/infima.tex`, `prop:equal-infima`, proves approximation
for this gapped example. The full read `sections/riesz.tex`, `thm:riesz`,
already includes every d>=2 and every exponent s>0. Those extensions are
not new targets here. `source-contracts.md` and `source-retrieval.json`
record reading extent, exact paths, pinned URLs and Git blob identities.

The new operation identified before freezing was **contact completion**:
fill all gaps and tails while preserving an exact obstruction to maps.
The old finite contact certificate is only on V^3. A positive background
charges its complement. Continuity of costs or weak convergence does not
preserve exact contact identities or the graph property.

Historical I217 concerns sharp cost versus BV/fractional map complexity for
the original gapped density. Its partial report and analytic attempt were
read. P has no complexity restriction and does not reuse its disconnected
support obstruction. Neither old target is declared solved. F/G and their
technical verdicts, all other supplied vetoes, and the parent's corrections
remain unchanged.

## 3. The local obstruction tolerates leakage

Here is the exact measure step needed after filling gaps. It is an
elementary extension of the source's selection argument, not a substantial
result nominated on its own.

**Lemma 1.** Let a probability mu have a density f on B, and let Q be a
compact Borel subset of B. For each j let

    b_j(x)=rho(H_j(x)) |det DH_j(x)|, x in Q,

where rho is the density of mu on H_j(Q). Suppose b_j(x)<f(x) almost
everywhere on Q for every j. A preserving Borel map T can equal H_j(x)
only on a mu-null subset of Q.

Proof. On S={x in Q:T(x)=H_j(x)}, change of variables and preservation give

    integral_S f dx = mu(S)
       <= mu(T^-1(H_j(S))) = mu(H_j(S)) = integral_S b_j dx.

The image is Borel because H_j is a homeomorphism onto an open image.
Strict density domination forces S to be null. This proof applies to
arbitrary Borel selections, without differentiating T. QED.

**Lemma 2.** Suppose w is a bounded global admissible potential which
equals u on V, and mu has a finite optimal coupling saturating w. Under
Lemma 1, an optimal preserving pair must satisfy

    mu(Q) <= 2 mu(V^c).                                      (3.1)

Proof. A saturated optimal Monge pair has zero nonnegative slack almost
everywhere. If x in Q and both outputs lie in V, the source certificate
forces T2(x) into the four H_j(x). Lemma 1 makes this event null. Thus
almost every x in Q has T2(x) or T3(x) outside V. Preservation and the
union bound give (3.1). Additional incoming mass never helps the selection
inequality. QED.

This is useful for genuine positive backgrounds. Fix a compact Q inside
{g_b>0}, with b=nu(Q)>0 and m=inf_Q g_b^2>0. If sigma=h^2 dx is any
probability with h>0 Schwartz, set

    mu_epsilon=(1-epsilon)mu_0+epsilon sigma,
    K=max_j sup_Q h(H_j(x))^2 |det DH_j(x)| < infinity.

The central and branch pullback densities obey

    f_epsilon-b_{epsilon,j}
      >= (1-epsilon)m/6-epsilon K >0

when epsilon<m/(m+6K). Also mu_epsilon(Q)>2 mu_epsilon(V^c) if
epsilon<b/(6+b), since mu_0(V)=1 and
mu_epsilon(Q)>=(1-epsilon)b/3. These are explicit sufficient inequalities,
not an unproved assertion of openness for optimal plans.

The square root of mu_epsilon's density is positive and Schwartz. To see
this, write mu_0=g_0^2 dx with g_0 smooth compactly supported. The square
root of (1-epsilon)g_0^2+epsilon h^2 is smooth because its argument is
positive. Outside a compact set it equals sqrt(epsilon)h; their difference
is smooth and compactly supported. It is therefore Schwartz. The exact
unpaid hypothesis is that an optimal plan for this marginal saturates an
extension of u. Gaussian mixing alone does not provide that hypothesis.

## 4. Global admissibility is possible; a constant extension is insufficient

Choose M>=sup_V |u|, M>0, and put w_0=u on V and w_0=-2M off V.
It is bounded and Borel. It is globally admissible: triples wholly in V
use the source inequality; if at least one coordinate lies outside V,
their potential sum is at most zero and their Coulomb cost is positive
(or infinite). Thus a global lower bound is easy.

It is never saturated by an optimal plan of a finite-cost marginal
charging V^c. Every such coupling gives positive mass to triples meeting
V^c, where the slack is strictly positive. Since w_0 is bounded, the
integral of this slack is strictly positive for every finite optimizer.
The attained minimum is consequently strictly larger than 3 integral w_0
dmu. Admissibility must not be mistaken for dual optimality.

The naive simultaneous symmetric c-transform also fails to preserve
admissibility. For w=-a, a>0 constant, define

    Tw(x)=inf_{y,z}(c(x,y,z)-w(y)-w(z)).

Then Tw=2a: send y,z to opposite infinity for the upper bound, and use
c>=0 for the lower bound. The new threefold sum is 6a, exceeding the cost
of sufficiently distant triples. This is an exact Coulomb example, not
a numerical diagnostic.

## 5. A bounded global self-conjugate extension preserving the old sheets

The failed transform has an averaged repair. We prove it, including
regularity and noncompact infima, because it is a genuine checkpoint
toward the missing operation. It does **not** construct the marginal in P.

**Lemma 3.** The source u on V has a bounded globally Lipschitz extension w
with sum_i w(x_i)<=c, w=Tw, and w=u on all V. Every old contact remains a
contact. With C=2+1/sqrt(2),

    5/2 <= sup w <= C <3.                                  (5.1)

Proof. Start with w_0 from Section 4 and iterate

    h_n=Tw_n,       w_{n+1}=(2w_n+h_n)/3.

If w_n is admissible then h_n>=w_n. For each triple the definition gives
c>=h_n(x)+w_n(y)+w_n(z), and the other two permutations. Adding and
dividing by three proves admissibility of w_{n+1}. Thus w_n increases.
At any old contact (s,t,r), preservation of its three old values forces
h_n(s)<=c(s,t,r)-w_n(t)-w_n(r)=u(s). Combined with h_n>=w_n, induction
pins all coordinates of all old contacts. Their projections are all V,
so w_n=u and h_n=u there.

For arbitrary x choose a=-sign(x_1)e_1 and b=-sign(x_2)e_2, with either
sign if a coordinate vanishes. These are distinct old outer centers with
w_n(a)=w_n(b)=0, |x-a|>=1, |x-b|>=1, |a-b|=sqrt(2). Hence

    h_n(x)<=c(x,a,b)<=C.

All iterates are bounded below by -2M, and w_n<=h_n<=C. Moreover h_n
decreases, since T reverses order. The increasing bounded w_n has a
pointwise limit w, and w_{n+1}-w_n=(h_n-w_n)/3 tends to zero. Therefore
h_n tends to the same limit. For a fixed x, infimum over n and infimum
over (y,z) commute. Since w_n increases, this proves

    lim_n h_n(x)=inf_{y,z}(c(x,y,z)-w(y)-w(z))=Tw(x).

There is no compactness assumption in this interchange. Global
admissibility passes to the pointwise limit at every collision-free
triple, and is automatic at a collision.

For completeness, the transforms have a common Lipschitz constant. A
delta-minimizer for h_n(x), 0<delta<1, has

    c(x,y,z)<=h_n(x)+w_n(y)+w_n(z)+delta<=3C+1.

Its three pair distances are at least eta=(3C+1)^-1. For |x'-x|<eta/2,
the gradient of the two x-dependent Coulomb terms is at most 8 eta^-2.
Testing h_n(x') with this pair and letting delta decrease to zero gives
h_n(x')-h_n(x)<=8 eta^-2 |x'-x|. Reverse x,x' and chain short segments
to get a common global Lipschitz constant. This also establishes
measurability without an unproved measurable-infimum assertion. The
initial w_0 is Borel and all further w_n are Borel. The common pointwise
limit of the h_n is Lipschitz. Preservation of u(0)=5/2 proves the lower
bound in (5.1). QED.

The averaging argument is a dual-feasibility operation. Neither its
fixed point nor its Lipschitz regularity is claimed as a substantial
new-to-literature theorem. Existing duality supplies self-conjugate
potentials for an already specified marginal; the point of this deduction
is exact preservation of the stipulated local sheets.

## 6. The extension has finite contacts at infinity, with a compact defect

Define h_2(y,z)=|y-z|^-1 and

    a=inf_{y!=z}(h_2(y,z)-w(y)-w(z)).

The lower bound a>=-2C is finite. The old values at 0,e_1 imply a<=-3/2.
The identity w=Tw and the nonnegative two remaining pair terms imply
w(x)>=a. Conversely any fixed distinct y,z gives

    w(x)<=h_2(y,z)-w(y)-w(z)+1/|x-y|+1/|x-z|.

Taking the limit superior as |x| tends to infinity, then the infimum over
fixed pairs, proves the uniform-at-infinity limit

    w(x) -> a.                                               (6.1)

Here uniformity means the usual limit outside a sufficiently large ball;
one fixed almost-minimizing pair supplies the upper estimate there.

Let R be the projection of the set of minimizing pairs for a. This set
is nonempty and compact. Indeed 2a+C<=-3+C<0. If |x| is large, (6.1)
gives w(x)<=a+delta, where delta>0 is chosen so that
-a-delta-C>a. Uniformly over z,

    h_2(x,z)-w(x)-w(z)>=-a-delta-C>a.

The same estimate in either coordinate confines all minimizing sequences
to a fixed compact set. They stay away from collisions because w<=C and
the objective tends to a finite value. Continuity then gives attainment
and compactness of the minimizing-pair set and its projection R.

For any fixed x outside R, the infimum defining Tw(x) is attained by a
finite pair y,z. To verify this, take a minimizing sequence. Both partners
escaping would give limit inferior at least -2a>=3>C>=w(x). If exactly
one escapes while the other tends to z, collision bounds ensure z!=x,
and the limiting objective is

    1/|x-z|-w(z)-a.

Equality to w(x) would make (x,z) a minimizing pair for a, contrary to
x not in R. Thus a bounded subsequence exists; uniform separation and
continuity produce a finite contact. Points in V already have contacts
from the source, whether or not they belong to R.

This pays finite contact existence outside the compact possible defect
R\V. It does not show that defect is null or empty, or that contact
selections project to smooth densities. In particular, there is no
unproved passage from a self-conjugate potential to a coupling for an
arbitrary prescribed marginal. The constant w=0 is already a simple
warning: it is globally self-conjugate for Coulomb cost, yet no finite
triple saturates it.

## 7. The exact remaining completion problem

A sufficient unpaid operation is the following, for the w constructed
above:

    Construct a probability eta supported on {c=sum_i w(x_i)} whose
    three marginals all equal sigma=h^2 dx for some h>0 Schwartz,
    integral h^2=1.                                          (CP)

This is stated as an **unproved construction problem**, not an assumption
of a claimed theorem. It is not a restatement of P: eta may be Monge,
and CP concerns this particular preserved calibration. It is only one
sufficient route to P, not a necessary condition for every possible proof.

To prove sufficiency, choose epsilon satisfying the two strict bounds
in Section 3 and put

    pi_epsilon=(1-epsilon)pi_0+epsilon eta,
    mu_epsilon=(1-epsilon)mu_0+epsilon sigma.

Every term saturates the same bounded global w, so pi_epsilon is finite
and optimal for its common marginal. Lemmas 1 and 2 exclude every Monge
optimizer. The positive Schwartz square-root argument proves the exact
density class in P, and Section 1 supplies equality of infima. This is a
complete conditional reduction; it does not discharge CP.

Two barriers remain in CP. First, Section 6 allows an unresolved compact
set without known finite contacts. Second, even a measurable finite
contact choice for almost every first coordinate does not make its other
two pushforwards absolutely continuous, smooth, or small relative to the
source densities. Symmetrizing such a choice can add singular marginals.
A free-reservoir variational completion has the same issue: the reservoir
can concentrate on sets of smaller dimension, and no density estimate was
proved here. These requirements cannot be inserted as hypotheses and then
reported as a proof of P.

## 8. Two other routes that do not complete P

**Mixing local optimizers need not retain optimality.** This can be seen
within the exact Coulomb model. Let E_0>0 be the cost of symmetric pi_0,
and let its marginal support have diameter D. Translate the whole example
by a vector of length R>D. The half-and-half mixture of the two optimal
plans has cost E_0 for the half-and-half mixture marginal. Instead use,
with equal probability, an AAB or ABB triple, then uniformly permute its
coordinates. The internal pair is drawn from the corresponding pair
marginal of pi_0; the singleton is independently drawn from the other
translated marginal. Symmetry makes the expected internal pair cost
E_0/3. The two cross distances are at least R-D. The new plan has exactly
the same common marginal and cost at most

    E_0/3+2/(R-D)<E_0  when R-D>3/E_0.

Thus even smooth source examples cannot be combined as optimizers without
a common calibration. This refutes that proof operation, not P.

**Weak limits do not preserve graph structure.** On [0,1] with Lebesgue
measure, T_n(x)={nx} preserves measure. For every continuous F,

    integral F(x,T_n(x))dx
      =n^-1 sum_{k=0}^{n-1} integral_0^1 F((k+t)/n,t)dt
      -> integral_0^1 integral_0^1 F(s,t)dsdt.

Uniform continuity and ordinary Riemann sums justify the limit uniformly
in t. Product measure is not supported on any Borel graph, by Fubini,
although every approximating graph measure is. Therefore convergence of
perturbed optimizers to a non-Monge source optimizer does not exclude
deterministic perturbed optimizers. This is a general closure obstruction,
not a Coulomb counterexample to P.

## 9. Primary-literature operation comparison and honest limits

The bounded screen read GKR's 1805.00417v1 Theorem 1.1 and the actual
shared-component construction in Section 3, including Theorem 3.5 and
Lemma 3.6. Its harmonic repulsion and disconnected intervals supply the
selection antecedent; they do not give a positive smooth Coulomb marginal.
The pinned source explicitly adapts that mechanism and already pays its
local Coulomb calculus. Neither is claimed new here.

Colombo--Di Marino's Theorem 1.1/Remark 1.3 pays equality of infima.
GKR's duality paper, Theorem 4.2, pays dual attainment under its stated
concentration/integrability conditions. Theorem 5.2 and Lemma 5.3 provide
Lipschitz/self-conjugate optimal potentials for a specified marginal.
Proposition 5.4 concerns value continuity under its hypotheses. None of
these inspected contracts keeps prescribed local values while constructing
a smooth positive marginal supported on their contacts. They must not be
cited as CP. The averaging proof above does not supply CP either.

The operation screen rejected three other paths before sustained proof:
the bi-Sobolev target is an old unresolved lane; matrix Lieb--Thirring
equality is explicitly classified by a pinned companion `thm:main`;
and generic iid RWRE CLT transfers were already excluded in I232. Those
files were read only to avoid duplication. No new theorem was nominated
from those families. The complete 13,223-entry nontruncated preprints
tree was parsed for inventory, with 749 manuscript directories. Parsing
or authenticating a file is not a claim to have read its mathematics.

No exact statement of P was found in the bounded primary screen. That
is not a novelty argument, worldwide priority certificate, or independent
contribution PASS. P would require the global contact/density operation;
it is not established by merely having a sophisticated dual object.
The supporting deductions are technical research. There is no proof PASS
for P, and no counterexample to P. Finite simulations were unnecessary;
none was used as evidence for the existence statement. There is no Lean
claim, partial or full, and no package advancement is requested.

## 10. Provenance, verification and handoff

The full mandatory historical brief, full G candidate and both independent
reviews, both parent dispositions and F corrections were read. Historical
ownership instructions were not treated as permissions. The three supplied
G/review seals are authenticated as external read-only packages, without
executing their code or copying their trees. Parent corrections control
the historical interpretations: F's universal tree-gap assertion is false;
G gives a distributional norm law, not an explicit norm CDF; the ordinary
unit-resistance analogy is bridge-only; unread pruning papers are not
evidence. None is reopened here.

`inputs-manifest.json` binds local private reading inputs and exact external
read-only references by size and SHA256. `outputs-manifest.json` binds the
original report, frozen scope, progress and verifier. The detached terminal
seal anchors `seal.json`, which binds both manifests. `verify.py` authenticates
the external anchor, both inventories, exact membership, source Git blobs,
frozen scope and historical seals before reporting integrity. It executes
no stored checker, downloads nothing and writes no files. Bad-anchor and
controlled-failure diagnostics preserve every frozen tree. These are
artifact checks only, not mathematical or contribution gates.

The parent alone integrates findings. The count stays 4/10. The next
mathematical task, if P is ever resumed, is CP or a different actual proof
of the full frozen target; no third-party source or conditional lemma has
silently paid it.
