# W007 component factorization — parent disposition

2026-10-08. Accepted mathematical core, with the scope repairs below.
Verified new factoring complexity improvement: **NONE**.

The [independent Opus report](W007-component-review.md) and all nine delivered
files passed their SHA-256 manifest check. Original report bytes are preserved.
The parent accepts the all-depth factorization, component count
L_k=1+k(k+1)/2, total degrees, distinctness, and absolute irreducibility in
odd characteristic. Homogeneity supplies the missing total-degree argument.
The exact component mean and elementary pair-intersection estimate are accepted;
the sharper pair constant is Pi_k=(4^(k+1)-3k-4)/9. The fixed-k root mean is
L_k+O_k(p^(-1/2)). Removing the old degree restriction uses a trivial bound
outside the useful Weil range; it does not extend the useful asymptotic range.

The collision-weighted refinement gives, for k>=1 and k*2^k<=sqrt(p)/4,

    L_k-A_k/sqrt(p)-Pi_k/p <= E[m_k] <= L_k+A_k/sqrt(p),
    A_k=(k-3)*2^k+k+3-(k^3-k)/6 <= k*2^k.

These expectations concern the full independent training tape. The k=0 case
is the exact identity m_0=1 and is separate from expressions involving 1/k.
The report's conditioning on r_0!=0 has a valid intersection denominator
p-1; it is not conditioning on the composite algorithm's survival.

The following claims in sections 8–9 are NOT adopted unqualified:

- Global survival couples the CRT components. The local history need not
  depend only on a local survival event. Use a full-tape coupling and union
  bound; do not transfer these means to a survived-history law.
- The fixed-schedule M bound charges a nominal evaluation budget. It is not
  automatically a lower bound for executed work if a run is abandoned early
  on gcd N. Actual work is addressed by the separately audited, explicitly
  specified implementation in the [Fourier disposition](W007-fourier-envelope-disposition.md).
- A small additive-triple excess alone does not establish E[m_k]=L_k+o(1)
  up to k approximately log2(p): the intersection term and absorbed-root
  moments are uncontrolled there. Nor does it close every depth.
- A threshold on mean roots alone omits training, per-probe work and early
  successes. The actual ledger, not that threshold, determines comparison.
- Local discriminant bias is not proved equivalent to additive structure
  for all algorithms. Known global roots and unavailable local information
  identify a missing acquisition procedure, not an impossibility theorem.

The useful result identifies why exponentially growing degree did not give
exponentially growing average roots in this range. It leaves changed sampled
updates, later depths and implicit scalar product computation open. The parent
is developing those independently; no further polynomial-tower review is
required before proceeding. No candidate experiment, shared code or Lean change.
