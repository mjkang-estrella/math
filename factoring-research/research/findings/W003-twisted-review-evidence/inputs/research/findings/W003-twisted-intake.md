# W003 Lens A — coordinator intake

2026-10-08. **UNACCEPTED pending independent review.**
Verified COMPLETE factoring complexity improvement: **NONE**.

The coordinator consumed all 511 lines of
[the submission](W003-twisted-fields.md), its source notes, and its input
inventory. The constructor's task is completed with no pending child runs.
The original report remains unchanged. Its byte-identical
[submitted snapshot](W003-twisted-submitted-draft.md) has SHA-256
7197a3de72f354d762ae6a12a089602275d3d435a01e033cae45a5b6b1f529d3.
All 29 input snapshots and 32 original delivery entries verified.
The W003 brief remains at
fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629.
Hashes establish identities, not mathematical correctness.

## Submitted finite realization

After paid elementary cases, an n-bit raw word x either fails the range/gcd
checks, gives a factor, or supplies R=x^2 mod N on the unit branch. The inner
algorithm sees only N,R. It chooses u=R+2N, D_1=u^2+N, D_2=u^2+3N, and
f_i(T)=T^2-D_i. The nonsquare gaps for D_i and D_1D_2 are claimed to prove
irreducibility and distinct fields without factoring the defining integers.
Heights are O(N^2), derivatives reduce to the unit 2R, and selection is paid
polynomial work without retries.

The ordered row list is (j,1), 1<=j<=n. Gcd(j^2-R,N) returns a proper factor,
returns the directly recognized root j on full gcd, or retains a unit row.
After an entirely retained list, the literal algorithm scans every subset
and both mixed-target orientations. An elementary exact quadratic-field
square test is specified; no square-class basis or field-root oracle is used.
Derivative multiplication and cancellation precede reduction of field roots.

The proposed decisive obstruction is real sign: at alpha_i -> -sqrt(D_i),
each a^2-b^2 alpha_i is positive and alpha_i z^2 is negative. Thus neither
mixed orientation can succeed for any nonzero rational pairs or integer
exponents. Common rational scalar factors do not remove the simultaneous
sign mismatch. This is a scope-limited obstruction to the selected fields
and relation form, not a lower bound for all W003 constructions.

## Claims needing independent audit

1. Check every strict gap, coefficient bound, congruence and domain in the
   selection rule. Verify that the two fields are distinct, not merely the
   polynomials, and that elementary preprocessing covers repeated factors.
2. Audit the complete rational square-root test, including B=0, zero,
   negative radicands, completeness, coefficient widths and finite bit cost.
   Check localization, integrality, cancellation and both target orientations.
3. Prove the sign obstruction at precisely its claimed scope, including
   inverses and common scalar factors; retain its explicit escape boundaries.
   Do not turn a simple known signature character into a novelty claim.
4. Check the ordered early-return law. The report claims
   sigma_N=(N-1-phi(N)+|U_N|+(2^r-2)|J_N|)/2^n and, for distinct p,q>2n,
   sigma_N=(2n+1)(p+q-2-2n)/2^n. Confirm the same-j/global-sign failures and
   different-j early factors, without unproved independence.
5. Audit fixed finite-tape costs, h=n on every subset-search branch, literal
   2^(n+1) failed twisted-root calls, and positive probability of that branch
   for growing balanced semiprimes. Check the stated expected split lower
   bound Omega(N^(3/2)/n), upper N^(3/2)poly(n), polynomial space, and recursive
   all-input factorization accounting.
6. Verify that pruning with the real-sign certificate preserves successes,
   leaves only the stated gcd/root-recognition sampler, and has the claimed
   N_0^(1/2)poly(log N_0) complete expected upper envelope. Its success does not
   count as mixed-field inversion or a new complexity improvement.
7. Check primary attribution and inherited H027/H028/H031 boundaries. The
   source lens is a separate research submission, not a review of this one.

The first read found no established contradiction requiring a parent repair.
That is not acceptance. The exact cost and probability deductions require
independent checking. No experimental result or Lean theorem is supplied.
No experiment is selected: a valid sign obstruction cannot be repaired by
enlarging this same row cap. A changed field/element law would be new work.
