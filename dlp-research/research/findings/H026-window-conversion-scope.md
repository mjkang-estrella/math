# H026 fixed-anchor window conversion: corrected limited contract

2026-10-08. Initial Fable proposal and NEW independent Opus review are preserved
in H026-information-fable-raw.md and H026-window-review-raw.md. Root accepts the
following elementary corrections only. No computable feature H with supported
gain is supplied; no numerical run is admitted. Character-theorem closures,
calibration guarantees and universal information classifications in the raw
reports are not accepted here.

Let 1≤Delta<q, M=ceil(q/Delta), and fix an offset s. Partition the lifted interval
s+[0,q) into M blocks, each of length Delta except the last, of length L≤Delta.
Reduce points modulo q after making this partition. Anchor a_i=s+i*Delta and
block length L_i are explicit; the final local search is restricted to L_i.
This convention removes overlap at the cyclic seam. Query bucket H([m]G),
then search each matching anchor's interval with exact verification.

For uniform m the exact success probability of this specified partition decoder is

`p_s = (1/q) sum_i sum_(0≤delta<L_i) 1[H([a_i+delta]G)=H([a_i]G)]`.

If pi_b=Pr_m[H([m]G)=b] and N_b(s) is the number of anchors in bucket b,
the expected number of local searches when all matching anchors are processed is
`nu_s=sum_b pi_b*N_b(s) ≤ M*max_b pi_b`.
The number of possible buckets by itself does not control occupancy.

Uniform independent random shifts of Q make retries iid for a fixed table.
Charge their scalar multiplication/randomness cost c_rand and H evaluation c_H.
For an implementation processing a complete attempt, with actual expected cost
C_s, the expected work through the first successful attempt is C_s/p_s by the
renewal identity. Using a common charged local-search cap c_loc gives
`C_s ≤ c_rand+c_H+nu_s*c_loc` plus lookup/verification/bookkeeping costs.
An upper envelope is not an exact runtime or a lower bound for smarter decoders.
Preprocessing, sorting, anchor generation, interval baby tables and memory are
additional, as are rebuild/calibration costs. Early stopping inside an attempt
can reduce this specified envelope and must be analyzed separately.

Set C_delta=(1/q)sum_n 1[H([n+delta]G)=H([n]G)]. The exact phase average is

`E_s p_s = ((M−1)*sum_(delta<Delta) C_delta + sum_(delta<L) C_delta)/q`.

It differs from the all-origin uniform-delta statistic by O(Delta/q), but neither
quantity determines any fixed table's p_s. Randomizing the target does not
randomize the table. Nor does E_s p_s determine E_s(1/p_s). A calibrated/rebuilt
table needs a specified confidence procedure and charged samples; the raw
informal calibration claim is not such a procedure.

Two corrections to the independent review itself:

- Since delta=0 is included, every anchor self-matches: p_s≥M/q>0. The raw
  p_s=0 assertion is false for this decoder. Caps/fallback can still be useful
  for controlling work, but not for that claimed nontermination reason.
- A two-sided decoder covers additional anchors/intervals. Its probability is
  not automatically ≤2p_s for a fixed grid: left and right correlations need
  not agree. Use its actual union of successful events instead.

H constant gives p_s=1 and nu_s=M. Thus a collision-probability gate alone passes
a feature that supplies no localization. The literal all-anchor interval-search
envelope is of order (q/Delta)*sqrt(Delta), at least sqrt(q). It is not a universal
lower bound against other ways to search the known full group.

For normalized cyclic Fourier coefficients of bucket indicators f_b,
the all-origin one-sided statistic is
`sum_b sum_a |fhat_b(a)|² Re((1/Delta)sum_(delta<Delta)exp(2pi*i*a*delta/q))`.
The zero-frequency baseline is sum_b pi_b², not necessarily 1/B. The one-sided
weights may be negative, so excess agreement is not simply positive low-band
energy. Drawing two independent offsets instead gives nonnegative squared
Dirichlet weights (the Fejer statistic), but that is a different statistic, not
this decoder's success probability.

## Research consequence

Any test of this mechanism needs an actual H, a reason for improved p_s relative
to occupancy and evaluation cost, a frozen table/retry procedure and matched
complete work. The raw optional small probe has no such premise. Information
from interval membership, soft ranking, other algebraic views or adaptive methods
is not ruled out by this correction. No standing universal gate is adopted.
Supported ordinary complexity remains square-root; verified full-work gain NONE.
