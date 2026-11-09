# W002 Lens B — corrected adaptive-generator scope and closure

2026-10-08. **ACCEPT the scoped mathematics with the completions below;
REJECT the multiplier-one realization as a new uniform factoring mechanism.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

This addendum governs the accepted result. The original report remains
unchanged, including its provisional status; its unsupported broader wording
is superseded here. The coordinator consumed all 693 independent-review lines.
All 69 review snapshots, 22 original snapshots, 10 source identities,
42 original delivery entries and 78 review delivery entries verified.
Review SHA-256:
e63dfe5cdb3a007239f70f6ef0167c8ef74f3ad382f5f8ef1cd0ba9ac8989e5a.
The original report and submitted draft remain byte-identical at
9d91b8b17dfeea5c36785a5c9a82512798b041fb230c67c8383c43b8bc588a80.
Unchanged intake SHA-256:
dcccf72ba83ec15ef67ad7e5b18be2b5a68f34e646826b6198b176d04b2ab958.

## R1: replace the noncontainment claim

N-dependent selection alone does not escape H026: its universe already
allows such selection from fixed first-n-prime-supported arithmetic pairs
(u_e,v_e) with the specified energy. An outside prime in an unrestricted
residual is not by itself a counterexample to pair containment. Accept the
following narrower arithmetic-support argument.

For arbitrarily large primes q other than 2 and 5, choose the unique even
a in [2,48] satisfying aq=2 modulo 25. Put s=aq and N=s^2+1. Then
N=5 modulo 25, so it is an odd non-perfect-power composite and passes this
trial's elementary preprocessing. Its first literal pair is (s^2,1), giving
residual -1. It has no later early gcd, by the all-cap recurrence below.
Uniformly in this bounded a, n=bit_length(N)=2log_2 q+O(1). The accepted
H026 bound p_n<=4(n+1)^2 implies q>p_n for sufficiently large q. Since q
divides s^2, that first pair cannot equal any H026 first-n-prime-supported
pair, even without its energy cutoff. Renaming the fixed alphabet does not
alter this contradiction. The proof uses no supplied q in the algorithm.

Thus no blanket literal-pair-preserving containment holds on this generator's
whole continuing domain. This neither disproves a different encoding nor
gives a witness in H026's balanced-semiprime ensemble. These witnesses have
empty positive bases and a factor 5; they establish no useful supply or
general claim that completed adaptive bases introduce new primes. The review's
separate outside-prime example concerns an admitted stream element only,
without proving completion of its H-step base. No stronger claim is adopted.

## R2: specify a sequential implementation of the costed trial

Adopt the fixed finite multitape schedule of independent-review section 6 as
part of this on-paper construction, with the following required operations.
Let h be attempted recurrence steps, S=sum bit_length(|r_i|) on a retained
no-factor prefix, and w=n+ceil(log_2(H+1))+2. Then h<=S<=h(n+1).
All record indices and scalar operands have polynomial width in w.

1. Stream the exact recurrence and append original-index records. Build a
   sorted distinct base tape using paid sequential selection, then construct
   the dense row-major decomposition by one complete base scan per row.
2. Find each first overlapping pair using only short base-list tapes: hold
   a and scan later b values, with all rewinds charged. This costs
   O((t+1)^2 poly(w)) for t current entries, without rescanning the matrix
   for every gcd.
3. Substitute each pair simultaneously using old exponents x,y:
   a^x b^y=g^(x+y)(a/g)^x(b/g)^y. Discard units and coalesce equal numeric
   columns, including coincidences with unchanged columns. For each row,
   one pass collects old affected exponents and a second writes the new row
   in merged base order. Base scans and rewinds cost O(h(t+1)poly(w)) per
   refinement. Keep only a constant number of current matrix copies.
4. The log-product potential decreases at least one each refinement, giving
   at most S refinements and t<=S. Their total cost is (S+1)^3 poly(w).
   Perform exact square tests on final base elements; save square roots and
   all full exponents, even where a parity column can be omitted.
5. Stream dense elimination with provenance: process original rows in order,
   scan prior pivot rows in leading-position order, and pay full current-row
   scans/xors/rewinds. Insert a nonzero pivot by ordered tape copying or
   append a zero-row provenance to the kernel tape. Cost is
   O((h+1)^2(S+h+1)poly(w)). A zero provenance has its own latest index as
   its last 1; these dependencies are independent. Distinct pivot positions
   and rank-nullity certify that they span the whole kernel.
6. For every basis vector, stream its selection mask, original roots and
   full-exponent rows. Make a sequential accumulator pass for each included
   row, then scan bases and aggregate exponents for modular powers, the
   congruence check and both gcds. Aggregate exponents have O(log(hn+1))
   bits. All at-most-h basis tests cost O(h(h+1)(S+1)poly(w)).

Retain original rows, exact decompositions, base values/roots, pivot and
kernel provenances, and failed gcd outcomes for FAIL(H). Their independent
counts sum to h; checking combinations and pivots at the same cubic envelope
verifies completeness of the fixed-list certificate. It does not certify
failure of every other factoring operation. No full refinement history,
huge unreduced convergent or exhaustive dependency list is stored.

These scans, arithmetic, output and a constant number of current tape copies
give time (H+1)^3 poly(n+log H) and space (H+1)^2 poly(n+log H).
For the registered H this is L_N[1/2,3] time and L_N[1/2,2] space, solely
finite-trial upper envelopes. Early-success paths omit later work. This is
not a runtime measurement, implemented program or Lean refinement.

## Accepted algebra and decisive limitation

The CFRAC recurrence has exact integer divisions, O(n)-bit stored states,
and X_i^2=r_i modulo N without storing huge convergents. Coprime refinement
preserves the exact signed square kernel while retaining original rows.
For every odd continuing N, the resulting root ratio defines a homomorphism
from this kernel to square roots of unity modulo global sign. The signed
overlap factor disappears in that quotient. Testing a full basis therefore
finds a useful root whenever any square subset of this fixed list would.
This does not prove the image nontrivial.

For N=s^2+1 entering the relation phase, m_i=s,d_i=1,a_i=2s for i>=1,
r_i=(-1)^(i+1), and X_i=s^(i+1) modulo N. Every square dependency has even
sum of i+1 and reconstructs X=+1 or -1, Y=1. Its productive image is trivial
for every positive cap. Kernel dimension is H-1: H=1 has no nonzero
dependency, while H>=2 has nonzero dependencies and unbounded growing nullity.
The infinite s=50t+2 family passes the stated preprocessing. The review's
CRT construction extends failure past each fixed finite prime screen; it
does not cover arbitrary growing screens or assert balanced-semiprime failure.

Adopt the additional prior-art attribution to Morrison–Brillhart Remark 3.13:
closure of failed square congruences under combination was already observed.
Remark 3.5 uses Fermat numbers as a short-period example; the general s^2+1
failure here follows from the displayed recurrence. No novelty is claimed.
The iid random-integer square-subset theorem is a different law and gives
no success theorem or lower bound for this deterministic stream.

The coordinator checked the literal-pair witness, simultaneous substitutions,
kernel/provenance completeness, sequential cost ledger, signed-overlap identity
and all-cap failure before adopting the repairs. The necessary useful-yield
condition is uniformly false for this unchanged algorithm. Larger caps and
more nullity cannot repair it. Different generators, multiplier laws, or
root distributions require new construction and success proofs; no global
factoring lower bound follows. No experiment or Lean task is selected.

[Original submission](W002-adaptive-relation-universe.md),
[independent review](W002-adaptive-review.md), [intake](W002-adaptive-intake.md).
