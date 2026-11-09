# W010 norm envelope: independent review

2026-10-08. **ACCEPT equations (1)-(5) at their stated raw-budget scope.**
The success claim also follows once the one-pin chart is specified as below.
Verified improved factoring complexity: **NONE**.

The original Deligne theorem has the stated constant and hypotheses. The
leading form satisfies them for every formal degree D=3^j, including degrees
larger than p. The useful O(k/p) moment conclusion is restricted to 81^k<=p.
Neither adaptivity nor stopping invalidates the derivation. No counterexample
to the five displayed equations was found; the arguments below prove them.

A concrete success bound for k raw training attempts, one attempted pin,
and at most T fresh probes is (R11) below. It includes pin rejection, full
gcds, training successes, and inactive paths. The accepted-pin root mean is
m+v/s, not m+v; the latter remains correct for an unrestricted pin. This is
a completion of the parent's explicit conditioning caveat, not a defect in
the five envelope equations.

## Frozen scope and evidence

The [input manifest](W010-norm-envelope-review-inputs-manifest.json) identifies
byte snapshots of AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
docs/SPECIFICATION.md, STATE, the original W010 hypothesis, the prior cubic
review and disposition, and the current parent envelope. Mathematical claims
refer to those snapshots. The explicit assignment overrides historical tasks
in STATE; no linked historical research was imported into this proof.

The [assignment record](W010-norm-envelope-review-brief.txt) fixes this round's
ownership and review questions. All writes use W010-norm-envelope-review*.
The parent may continue changing its own files independently. No candidate
run, finite-field or weight search, depth sweep, package installation,
delegation, shared source/Lean/state edit, commit, or publication was performed.

The [delivery manifest](W010-norm-envelope-review-manifest.json) hashes the
inputs, primary PDF, inspected page renders, extraction, report, and
[exact algebra certificate](W010-norm-envelope-review-certificate.py).
Its [saved output](W010-norm-envelope-review-certificate-output.json) records
27 passing checks of polynomial identities and rational constants only;
the mathematical proofs are given here. No shared project checks were run,
because no shared implementation or Lean code changed.

## Original theorem and smoothness

I retrieved Pierre Deligne, *La conjecture de Weil. I*, Publications
mathematiques de l'IHES 43 (1974), pp. 273-307, and visually inspected the
complete printed pp. 302-303, where Theorem 8.4 starts and concludes.
The [original PDF](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf) states
that a degree-d polynomial in n variables over F_q, with p not dividing d
and smooth top projective hypersurface, has complete nontrivial additive
character sum of absolute value at most (d-1)^n q^(n/2). It imposes no d<p
condition and no geometric irreducibility requirement.

The [frozen PDF](W010-norm-envelope-review-source-deligne-1974.pdf),
[page 302](W010-norm-envelope-review-source-deligne-page-31.png),
[page 303](W010-norm-envelope-review-source-deligne-page-32.png), and
[retrieval metadata](W010-norm-envelope-review-source-deligne-1974-metadata.json)
preserve this check. PDF physical pages 31-32 correspond to zero-based pages
30-31. The OCR is imperfect; the displayed exponent and constant were read
from the page images, not inferred from a search snippet.

Here is the application, proved separately. At a fixed realized training
state, P is monic with formal degree D=3^a, where a is its accepted-layer
count. For t!=0, the top form of t Q(P(X),P(Y)) is

    t H_D(X,Y),  H_D=X^(2D)+X^D Y^D+Y^(2D).

H_D(1,0)=H_D(0,1)=1. In the chart Y=1, put w=X^D. The roots satisfy
w^2+w+1=0. They have w!=0, and

    (2w+1)^2-4(w^2+w+1)=-3.

Since p>3, the two w-roots are distinct, and 2w+1 is nonzero at either.
The derivative of X^(2D)+X^D+1 is D X^(D-1)(2X^D+1), nonzero at each
root because p does not divide D. Thus there are 2D simple geometric roots,
and no root at infinity. The resulting zero-dimensional hypersurface in
P^1 is smooth over F_p. Also p does not divide 2D.

Multiplication by nonzero t preserves that zero scheme. Lower coefficients
of P do not affect it. This proves all theorem hypotheses for n=2, d=2D,
q=p, without assumptions on how the coefficients were obtained. Formal
degree is used throughout; no reduction modulo X^p-X is legitimate here
unless its new leading form is checked separately. Growing D does not break
smoothness; it only worsens the numerical estimate.

## Fourier normalization and equation (1)

For a fixed nontrivial additive character psi, use

    eta_hat(t)=sum_b eta(b) psi(tb)
              =p^(-2) sum_(x,y) psi(t Q(P(x),P(y))).

Then eta_hat(0)=1. Dividing Deligne's complete-sum bound by p^2 gives
|eta_hat(t)|<=(2D-1)^2/p for t!=0. Character orthogonality gives exactly

    sum_b (eta(b)-1/p)^2
      = (1/p) sum_(t!=0) |eta_hat(t)|^2
      <= ((p-1)/p)*(2D-1)^4/p^2.                         (R1)

The factor (p-1)/p in the parent is indeed only dropped to weaken the
bound. Since eta is a probability law,
sum eta^2=1/p+sum(eta-1/p)^2.

With nu(0)=0, K(b) is precisely the probability of the event
{Q(P(X),P(Y))=b and P(X),P(Y) nonzero and not equal or opposite}.
It is a subevent of {Q(P(X),P(Y))=b}. Consequently 0<=K<=eta pointwise,
so sum K^2<=sum eta^2. This proves parent (1), without normalizing K by
ell or deleting b=0 from eta.

As an algebraic normalization check, at P=X the conic count gives
eta(0)=[p+(p-1)epsilon]/p^2 and eta(b)=(p-epsilon)/p^2 for b!=0,
epsilon=chi(-3). Therefore the left side of (R1) equals (p-1)/p^3,
attaining (R1) for D=1. No enumeration is needed.

The conclusion is an L2 energy bound. It is not relative pointwise
equidistribution, nor a bound with the same normalization on K/ell. For
example, when epsilon=1, eta(0)/(1/p)=2-1/p already at P=X. Near the
degree cap the bound need not give vanishing total variation distance.
The exact estimates, rather than an informal meaning of "almost flat,"
are what support the subsequent argument.

## Statewise drift and equation (2)

The prior review's identities survive rechecking: the new off-diagonal
collision mass is K+A+2mB, the new zero mass is m+B, and B^2=2A.
All pairs in K are ordered. At beta=0, A=B=0; no exceptional root
contribution occurs. Thus Delta v=K-A and Delta m=B at fixed beta, giving
D_v=sum K^2-sum KA and D_m=sum KB under raw legal acquisition.

The prior orbit proof also checks: interchange and simultaneous negation
give four-element legal orbits, with same-orbit energy 4S, where
S=v^2-2q4. Distinct-orbit energy R is nonnegative. At beta=a^2!=0 the
legal quadratic relation has degree at most two and excludes +/-a, hence
K(beta)<=2(v-A(beta)). Summing against A yields sum KA<=2S. Therefore
D_v>=2S+R>=0 (strict when ell>0). No pointwise weighted-law monotonicity
is used, and the earlier suggestion of a negative raw drift stays withdrawn.

Every nonzero a contributes once to sum B, so sum B=s=1-m. Odd symmetry
groups the two square roots with equal masses, giving sum B^2=2v. Put
delta(b)=eta(b)-1/p. Nonnegativity, domination K<=eta, and Cauchy-Schwarz
then give

    0<=D_m<=sum eta B=s/p+sum delta B
              <=s/p+||delta||_2 sqrt(2v)
              <=s/p+(2D-1)^2 sqrt(2v)/p.                  (R2)

The subtraction term sum KA is nonnegative, so
0<=D_v<=sum K^2<=1/p+(2D-1)^4/p^2. This proves parent (2).
No root of beta is computed by the protocol, and no auxiliary
three-variable sum or uniform-beta premise enters the proof.

## Adaptivity, freezing, and equations (3)-(5)

Let F_j contain the entire history before raw slot j, the realized joint
map, and whether the run is active; write I_j for its active indicator.
On distinct primes p,q>3, fresh uniform CRT samples supply independent
local pairs conditional on F_j. Their joint legal probability is ell_p ell_q.
Updating only on that chart, and leaving the map fixed on every other
outcome, gives

    E[v_(p,j+1)-v_(p,j) | F_j] = I_j ell_(q,j) D_(v,p,j),
    E[m_(p,j+1)-m_(p,j) | F_j] = I_j ell_(q,j) D_(m,p,j).   (R3)

After a proper factor, the map is frozen for all remaining scheduled slots;
the actual implementation terminates. This makes inactive increments zero,
not inactive masses zero. The analogous equations hold at q. Conditional
independence of entire survived histories is neither claimed nor needed.

Before slot j there have been at most j accepted updates, so D<=3^j.
Using (R3), 0<=ell<=1, and the nonnegative drifts,

    E[v_(j+1)-v_j] <= 1/p+16*81^j/p^2.

Since v_0=(p-1)/p^2<=1/p and 16/(81-1)=1/5, summing proves

    E[v_t]<=V_(p,t):=(t+1)/p+(81^t-1)/(5p^2).             (R4)

Likewise, s<=1 and (2D-1)^2<=4*9^j imply

    E[m_(j+1)-m_j] <= 1/p+(4*9^j/p) E[I_j sqrt(2v_j)]
                        <= 1/p+(4*9^j/p) sqrt(2 E[v_j]).

The last step drops I_j using nonnegativity and applies Jensen to the
whole frozen-state distribution. Starting with m_0=1/p gives

    E[m_t]<=M_(p,t):=(t+1)/p
                   +(4/p) sum_(j=0)^(t-1) 9^j sqrt(2 V_(p,j)). (R5)

These are exactly parent (3)-(4). They are not survival-conditioned means.
At t=0, M_(p,0)=1/p with an empty sum and V_(p,0)=1/p; retain the sharper
actual v_0=(p-1)/p^2 whenever desired. No division by ell occurs, so a state
with ell=0 causes no undefined expression in this argument.

For k>=1 and 81^k<=p,

    V_(p,k)<=(k+6/5)/p.

For every 0<=j<k, V_(p,j)<=(j+6/5)/p<=(k+1/5)/p. Therefore

    M_(p,k) <= (k+1)/p
           +(4/p) sqrt((2k+2/5)/p) * (9^k-1)/8
           <= (k+1+(1/2)sqrt(2k+2/5))/p.                 (R6)

This proves both constants in parent (5). The raw cap implies
(3^k)^4=81^k<=p, hence every realized training map has D<=p^(1/4).
All (R4)-(R5) remain valid outside this cap, but may be uninformative.
They do not justify the O(k/p) simplification at greater depth. Conversely,
a cap on accepted layers alone is not a cap on the number of paid raw
attempts; the time parameter in (R4)-(R6) is raw slots.

## A fully specified training, one-pin, and probe protocol

Fix integers k,T>=0 before running. They may be chosen from N; knowledge
of its factors is not an algorithmic input. Analyze N=pq for distinct
p,q>3. The inequality 81^k<=min(p,q) is a domain condition for the short
depth conclusion, not an oracle granted to the algorithm.

1. Start with P(X)=X. In each of at most k raw slots, sample fresh
   independent uniform r,s modulo N and form z=P(r), u=P(s). Test
   z,u,z-u,z+u individually by gcd, in that order. Return immediately on
   a proper gcd. A full gcd does not suppress the remaining tests in that
   slot. If all four gcds equal 1, append the specified cubic update;
   otherwise leave P unchanged and charge the slot.
2. If still active after k slots, take exactly one fresh uniform r modulo N
   and form a=P(r). If gcd(a,N) is proper, return it. If it equals N,
   terminate this run unsuccessfully. If it equals 1, set
   H(X)=P(X)*(P(X)-a). This is a product, not composition of P with P-a.
3. Make at most T fresh independent uniform probes x modulo N. For each,
   test gcd(H(x),N) and return a proper factor if obtained. Gcds 1 and N
   consume a probe and continue. Terminate unsuccessfully after the budget.

There is no pin resampling, extra beta/derivative/coefficient gcd, or
reuse of a training anchor as a fresh probe. Stopped paths are inactive.
The final product need not be odd; no training recurrence is applied to H.

### Training hazard

At an active local state the event that at least one of the four anchor
residues vanishes is exactly the complement of legality. Thus

    Pr(local anchor failure | state)
      =1-ell=2m-m^2+2v <=2m+2v.                         (R7)

The parent's 2m+2(m^2+v)<=4m+2v union bound is correct but weaker.
A proper gcd requires a local failure at p or q. The joint probability of
some nonunit anchor is 1-ell_p ell_q; it includes full gcd failures and is
not the exact proper-factor probability. A union bound over raw slots gives

    Pr(training success)
      <=2 sum_(l in {p,q}) sum_(j=0)^(k-1)
                               (M_(l,j)+V_(l,j)).       (R8)

Indeed the actual terms have I_j inside their expectations; dropping it
uses nonnegative masses. No conditioning on reaching slot j is hidden.
Additional whole-run termination on a full gcd can only delete a suffix
of tested events under the same coupled tape.

### Pin chart and its rejected mass

Freeze an active joint state after training. At a single prime write
nu(0)=0. The root mass of H for fixed a is h(a)=m+nu(a): for a=0
the map is P^2 and its zero mass is just m. Therefore

    E_a h(a)=m+v,                  a unrestricted;
    E[h(a) | a!=0]=m+v/s,          s>0;
    E[1_(a!=0) h(a)]=s*m+v.                             (R9)

The distinction exists already at the reachable state P=X: the unrestricted
mean is 2/p-1/p^2, while the nonzero-pin mean is 2/p. This is an exact
symbolic counterexample to transporting the first equality to accepted
pins without rejection weights, not a candidate experiment.

Let C be the joint unit-pin event and write b_l=s_l*m_l+v_l. At this fixed
state, CRT independence of the fresh pin yields

    Pr(pin proper factor)=m_p*s_q+s_p*m_q,
    Pr(C)=s_p*s_q,
    E[1_C h_p]=s_q*b_p,   E[1_C h_q]=s_p*b_q,
    E[1_C h_p*h_q]=b_p*b_q.

These weighted formulas are defined even if a component has s=0.
Conditional on an accepted fixed pin, a single fresh probe returns a
proper factor with probability h_p+h_q-2h_p*h_q. Hence the raw probability
of a proper factor in one scheduled clean-pin probe is exactly
s_q*b_p+s_p*b_q-2b_p*b_q, prior to any probe stopping. For T probes a union
bound is valid even though their unconditioned outcomes share the pin.
Dropping nonnegative rejection and overlap terms gives the convenient
active-state upper bound

    Pr(pin or probe success | training state)
      <=sum_(l in {p,q}) [(T+1)m_l+T*v_l].                (R10)

Apply (R10) with the training-active indicator and then drop that indicator
inside nonnegative expectations. No normalization by the training survival
probability or the unit-pin acceptance probability is introduced.

### Explicit full success bound and boundaries

Define M,V by (R4)-(R5). For the entire specified protocol, for all k,T>=0,

    Pr(success) <= min(1, B_(k,T)),

    B_(k,T) = sum_(l in {p,q}) {
        2 sum_(j=0)^(k-1) (M_(l,j)+V_(l,j))
        +(T+1) M_(l,k)+T V_(l,k) }.                     (R11)

In particular, if k>=1 and 81^k<=min(p,q), every j<=k satisfies

    M_(l,j)<=(3/2)(j+1)/l,
    V_(l,j)<=(6/5)(j+1)/l.

For j>=1 the first follows from sqrt(2j+2/5)<=j+1; the second from
j+6/5<=(6/5)(j+1). At j=0 use the exact initial masses. Consequently

    Pr(success) <= min(1,
       (k+1)*[(27/10)(k+T)+3/2]*(1/p+1/q)).              (R12)

This supplies explicit constants for the parent's
O((k^2+(T+1)(k+1))*(1/p+1/q)) claim at this protocol scope.
The final absorption map can have degree 2*3^k; no Deligne bound is needed
for it, so no extra final-degree restriction is being silently imposed.

For k=0, P=X throughout training and the specified chart gives the exact
full success probability

    (1/p+1/q-2/(pq))
    +(1-1/p)(1-1/q)
       *[1-(1-2/p-2/q+8/(pq))^T].                       (R13)

The first term is pin success. Conditional on a unit pin, H has two roots
in each field, giving per-probe proper success 2/p+2/q-8/(pq); fresh probes
are independent given the pin, and this probability does not depend on its
particular unit value. A full pin gcd ends the run and contributes zero.
At T=0, (R13) reduces to the pin-only law. Formula (R11) also applies at
k=0; substituting the exact v_0 sharpens it to
sum_l[(2T+1)/l-T/l^2], capped by 1.

## Disposition and next mathematical question

Accept the five envelope equations, the original-theorem application,
and the short-depth training-success order. Complete the one-pin success
claim with the chart above and (R11), or its simpler (R12). Retain the
unrestricted identity m+v only with its stated measure; (R9) is the precise
replacement when accepted pins are discussed.

The strongest result is a uniform, history-adaptive, stopped-process
short-depth moment and full-protocol success envelope for this actual
norm sampler. The formal degree's exponential growth has not yielded
exponential growth of these mean masses in the range 81^k<=min(p,q).
Positive expected drift remains compatible with this upper bound.

This is a raw-budget upper bound on success. It is not a lower bound on
expected actual work, a rejection of all cubic depths, an extension to
Jacobi-filtered acquisition, or a factoring hardness result. Tapes can stop
early. Obtaining k accepted layers can consume more than k raw attempts.
The sequential implementation pays for every fresh circuit evaluation;
no lower bound on all evaluators or batch detection follows from this review.

The remaining mathematical question for this sampler is whether reachable
laws beyond the useful degree cap can acquire and retain enough norm energy
and root mass, with their actual legal probabilities and paid acquisition,
to improve complete success per work. The present proof supplies no such
lower-rate theorem. A quantitative deeper-law argument, or a changed costed
acquisition mechanism, is needed before selecting a depth sweep. The parent's
separate batch-detection work is outside this review.
