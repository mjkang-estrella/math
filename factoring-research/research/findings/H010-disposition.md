# H010 — finite dense-bucket cap rejected, marginal question open

Date: 2026-10-08. Verified factoring complexity improvement: **NONE**.

Accept the [report](H010-marginal-width.md)'s narrow finite disposition. Its
N-only clean arithmetic network and unit-multiplication cancellation lead to

    P_k(s) = 2^(-2k) sum_(u,u'<2^k)
      [a^(2^(m-k)*u) = a^(2^(m-k)*u') mod N]
      exp(2*pi*i*(u-u')*s/2^k).

The coordinator checked the common-suffix cancellation and normalization:
the work trace equates output residues, not reversible scratch states. An
all-zero Fourier history removes unary phases but does not identify the two
measured input branches. The identity is not an efficient evaluation algorithm.

The frozen min-fill procedure for N=143, a=35, k=2 reaches an 11-variable
bucket, exceeding its registered cap 10. The resulting output factor has only
10 variables. Source/protocol hashes match, and a separate bitset audit replayed
the witness. Preserve all 688 cases: 2 completed, 1 rejected, 685 unstarted.
The later sizes did not run; there is no scaling fit or hidden success rate.

This does not reject an output-factor cap of 10, a different elimination order,
another arithmetic circuit, or an O(log n) width bound with different constants.
Indeed k=2 leaves only 16 input pairs; directly conditioning the four input
bits computes this very probability cheaply. The failure exposes a poor
intermediate representation for this case, not inherent marginal difficulty.

Conditioning all 2k input bits generally costs 4^k evaluations. It is polynomial
for k=O(log n), exponential when k is proportional to n. Reopen only with a
specific smaller cutset, exact arithmetic simplification, or costed batching
rule that handles the large-prefix regime. Simply raising the old cap cannot
establish that. All histories, precision, planning, sampling and factor-recovery
costs would remain necessary for a positive algorithmic claim.

The arithmetic validations and symbolic prefix checks are finite evidence,
not a Lean refinement or a general simulation theorem. No further amplitude
implementation is justified by this screen alone. This route is now reserve
work pending a new primitive; its task is complete.
