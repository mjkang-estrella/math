# W007 — a uniform early-depth envelope from the exact Fourier drift

2026-10-08. Parent derivation after task E was frozen. PROVISIONAL.
This is a different proof obligation from the component irreducibility
audit: use the accepted one-step drift to bound a growing-depth range.
No factoring experiment, solver or Lean change, or new factoring upper bound.

## Conditional estimate, with normalization explicit

Use the same UNSTOPPED adaptive tower P_(i+1)=P_i(P_i-P_i(r_i)).
For its current polynomial f=P_i on F_p, let n(y)=#{x:f(x)=y},
C_f=sum_y n(y)^2, and

    T_f=sum_(y,w) n(y)n(w)n(y+w),
    D_f=sum_y n(2y)n(y)^2 >= 0.

The reviewed full-collision identity, multiplied by p, says

    E[C_next/p-C_f/p | f]=(T_f-D_f)/p^2.                (1)

For S(t)=sum_x exp(2*pi*i*t*f(x)/p), orthogonality gives

    T_f/p^2=1+p^(-3) sum_(t!=0) |S(t)|^2 S(t),
    sum_(t!=0)|S(t)|^2=p*C_f-p^2.

f is monic of degree d_i=2^i. If d_i<p and p is odd, additive Weil
gives max_(t!=0)|S(t)|<=(d_i-1)*sqrt(p). Thus

    |T_f/p^2-1| <= (d_i-1)/sqrt(p) * (C_f/p-1).        (2)

Unlike the cruder bound using C_f<=d_i*p, this retains the CURRENT
collision mass, so it can be iterated without replacing it by degree.
The source is Kowalski's elementary notes, Theorem 3.2, printed p31:
https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf .
The parent read its conditions d<q, gcd(d,q)=1, nontrivial character;
they hold for the range in use. No result about generic coefficients is
needed for (2); it is uniform over all realized training histories.

## Growing-depth root bound

Define M_i=E[C_(P_i)/p], U_i=M_i-1, and delta_i=(2^i-1)/sqrt(p).
Since C_f>=p, U_i>=0. Taking expectations in (1)-(2) gives

    U_(i+1) <= (1+delta_i)*U_i+1,  U_0=0.

Consequently, for all stages for which 2^i<p,

    U_i <= i*exp(A_i),
    A_i=sum_(h=0)^(i-1) delta_h=(2^i-1-i)/sqrt(p).     (3)

Let m_i be the number of roots of P_i as a field function. The exact
absorption law is

    E[m_(i+1)-m_i | P_i]=C_(P_i)/p-m_i^2/p.

Dropping its nonnegative subtraction and summing (3) yields

    E[m_k] <= 1+k+sum_(i=0)^(k-1) i*exp(A_i)
           <= 1+k+k*(k-1)/2 * exp(A_(k-1)),            (4)

with k=0 treated separately. If 2^k<=sqrt(p), then A_(k-1)<=1/2 and
exp(1/2)<2. Hence the particularly simple uniform bound

    E[m_j] <= j^2+1,  0<=j<=k, whenever 2^k<=sqrt(p).  (5)

This reaches half-logarithmic depth, where degree first reaches sqrt(p).
It does not cover later depths by keeping the exponential constant. It
also does not imply that every realized branch has only O(k^2) roots.

## A scoped complete-cost consequence for a specified restarted trial

Consider only the following implementation: fixed k>=2 and t>=1, fresh
uniform training residues, the explicit triangular chain, then at most t
fresh depth-k probes, stopping early only on a proper factor. Full gcds
may be inspected via the already computed factors, but do not by themselves
end the trial. A failed trial completes its budget; independent trials
repeat the same k,t. There are no other gcd channels or coefficient-selection
rules. Both endpoint and pre-multiplication factor checks are allowed.

For N=pq with p<q and 2^k<=sqrt(p), set

    eta=1/p+1/q,
    A=eta * [k+k*(k-1)*(2k-1)/6],
    B=eta * (k^2+1).

Couple an early-stopped execution to the unstopped pre-sampled tape.
A proper gcd in training at stage j implies a zero at p or q in
P_j(r_j). Intermediate zeros persist to that stage endpoint. Likewise
any proper intermediate gcd during a depth-k probe implies a zero of
P_k at one component. A union bound using (5), without conditioning
the root law on survival, gives

    Pr[training factor] <= A,
    Pr[factor by the end of probe h] <= A+B*h.          (6)

These are upper bounds, not independent-hazard formulas. They account
for both CRT orientations and for successes before a masked full product.

Here is a proposed way to charge EARLY stopping rather than pretend every
successful trial pays its full budget. Assume A<=1/4 and B<=1/8, which hold
for sufficiently large p throughout the stated logarithmic range. Put
h0=floor(1/(4B)); then h0>=1/(8B).

- With probability at least 1-A>=3/4 there is no training success, so the
  explicit chain completes its k*(k-1)/2 multiplications. Expected training
  work is Omega(k^2).
- For every h<=min(t,h0), (6) shows probability at least 1/2 of no success
  by probe h. Each such failure completes that probe's k multiplications.
  Expected probe work is Omega(k*min(t,1/B)).

If t<=h0, the trial success bound A+Bt=O(eta*(k^3+t*k^2)), together with
expected work Omega(k^2+k*t), gives work/success=Omega(p/k).
If t>h0, expected work already exceeds a constant times k/B=Omega(p/k),
while success is at most one. The renewal identity for independent trials
therefore suggests the same expected Omega(p/k) modular-multiplication
lower bound, including early stopping. The constant is uniform for k>=2
in this regime. All inequalities and the coupling require independent audit.

This is a lower bound for this fixed-depth, fixed-budget restarted
implementation in its specified depth range, not for arbitrary adaptive
depths, rational updates, precomputed circuits, factoring, or the later
part of the same stochastic process. It does not compare bit costs by
treating unbounded arithmetic as constant time; the operation lower bound
already rules out matching the sqrt(p)*poly(log N) control on balanced
semiprimes in the stated implementation/range as p grows.

## Constructive interpretation

The decisive lost assumption is that polynomial degree represents useful
fiber growth under independent random training. Up to degree sqrt(p),
the actual conditional character sum limits the collision increase and
keeps expected roots quadratic in depth. A new acquisition rule must
change that conditional triple count, or use a materially different
computation than training/probing this tower. Increasing depth slightly
or inspecting another tiny-prime table does not repair the audited range.

Later depths remain mathematically open here. A rational map with a new
involution, or a paid parameter selector producing additive correlations,
requires its own full law; neither is asserted to succeed. The separate
compact-grid/scalar-product branch does not use this acquisition mechanism.
