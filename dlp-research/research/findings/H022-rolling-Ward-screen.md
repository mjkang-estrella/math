# H022 rolling Ward schedule: valid recurrence, unfavorable arithmetic

2026-10-08. Native Sol /root/h010_early_dependencies proposer and independent
native Astra /root/h007_additive_relations reviewer COMPLETED. Root checked
Ward substitution, window indices, scaling and the finite comparator below.
Brief/process in H022-independent-candidates.md. No numerical experiment,
Lean theorem or measured speed claim. Verified improvement NONE.

## Explicit support-sharing operation

For tau>=3, put ell=tau-1 and b=tau-2. Retain h_(a-r),0<=r<=tau.
Fixed public support C_m=h_m²,D_m=h_(m-1)h_(m+1) extends through tau.
With A=h_(a-ell+1)h_(a-ell-1) and B=h_(a-ell)², emit

    h_(a-2ell+r) = (A C_(ell-r)-B D_(ell-r))/h_(a-r),
    0 <= r < b.

Ward's identity with m=a-ell,n=ell-r proves this when the denominator
is nonzero. New old-relative offsets are2tau-2 down to tau+1. Moving the
anchor to a-b retains precisely old offsets tau-2,tau-1,tau, followed by
the b new terms. Reverse the output order or finish/buffer the whole block
before interpreting it as the next contiguous prefix. No boundary terms are
charged again as newly emitted keys.

The chosen computation costs A:1M, B:1S, output numerators and quotients:3bM,
and batch inversion:I+3(b-1)M. Total per window is

    (6b-2)M + S + I,

for b new keys. This is an implementation ledger, not a circuit lower bound.
It includes dynamic denominator inversion which the fixed-support idea alone
did not eliminate. Field additions and actual access/storage are additional.

## Common normalization and actual collision coverage

Use known h_i^G=phi(iG)/phi(G), and target phi(Q-jDG)/phi(G).
The target dynamic sequence is gamma times the normalized shifted DG
sequence, gamma=phi(DG)/phi(G). Fixed DG support remains UNSCALED. The
dynamic numerator scales by gamma², denominator by gamma, giving the right
output scale. Initialization pays gamma; no per-output conversion is needed.
For the known increasing prefix one can use reversal/sign symmetry, retaining
the same costs and avoiding the known identity as a recurrence denominator.
Retain the normalized-EDS/order hypotheses from the primary source.

Signed matches recover k=jD±i, followed by direct verification. This uses
known iG and target Q-jDG; earlier informal reversal of those roles did not
justify half-length target prefixes. Choose D=ceil(sqrt(2q)), known cap about
D/2 and target cap about q/D, with H019 rounding/endpoints. After buffered
prefix emission the coverage/stopping calculation is the same as the matched
baseline, up to explicitly paid block overshoot. These statements do not
assume that the paper's original depth-first ordering is contiguous.

Target zero at index j yields k=jD and must be verified. Known zero is only
an identity sentinel, NOT a recovered secret. Check zero denominators before
batch inversion. Noninjective EDS keys require retaining relevant equal-key
indices and paying all false-match scalar verifications.

## Finite arithmetic comparison

The independently checked H019 x-only expression with k=b,ell=1 is

    Cx = S + (10/3-2/b)M + 2I/(3b)

per emitted key. Subtracting it from the rolling cost gives

    (8/3)M - (1-1/b)S + I/(3b) > 0

for M>0,I>=0 and0<=S/M<=1. Equivalently compare three rolling windows
against one x-only block, each emitting3b contiguous keys. No infinite-batch
limit is needed for this arithmetic screen. Root checked the substitution
into H019 and the strict inequality (even S=M leaves a positive gap).

Public support generation takes paid O(tau) EDS arithmetic after bootstrap.
Initial shifted windows require public phi evaluations, with polylogarithmic
work per term, not free setup. Memory, initialization, feasible batch sizes,
exceptional dispatch, table traffic and terminal overshoot remain separate.
Choosing tau=o(sqrt(q)) alone does NOT guarantee setup is lower order if
per-term initialization is polylogarithmic; also require the complete setup
and block waste to be o(sqrt(q)) when invoking leading asymptotic constants.
Fixed or suitably polylogarithmic tau can meet that setup condition, subject
to the stated implementation. The finite kernel comparison needs no such
asymptotic assumption.

Decision: reject the literal rolling schedule's kernel-saving rationale.
This does not prove that every finite whole-runtime regime or other lazy EDS
scheme loses. The separate lazy-prefix proposal remains independently under
review. A numerical prototype is not justified by this unfavorable ledger.
Reopening requires a specific cheaper normalization/support mechanism with
matched full costs. No generic formal infrastructure is needed.
