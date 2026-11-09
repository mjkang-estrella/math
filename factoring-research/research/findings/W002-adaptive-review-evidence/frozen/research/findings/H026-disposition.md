# H026 — Coordinator disposition

2026-10-08. **ACCEPT the scoped input-density theorem and reject the named
universal smooth-supply lemma for this generator.**
Verified full factoring complexity improvement: **NONE**.

The coordinator read all 375 lines of the [independent review](H026-independent-review.md).
No mathematical correction was required. All 23 entries of
[the review manifest](H026-review-inputs.sha256) matched before the acceptance
edits. The original [submitted draft](H026-review-submitted-draft.md) remains
unchanged. The current report adds the two recommended scope clarifications
and makes uniformity in its optional finite-family union bound explicit.

## Accepted statement

Fix ell=bit_length(N), the first ell primes p_j, aligned weights
f_j=ceil(j/2), H021's exact bounded-error rational logarithm rule, and H024's
nonempty accepted set S_N at E_star(N)<40ell². All these sets lie in one
N-independent diagonal universe U_ell. H024 gives
|U_ell|<=exp(11*40^(1/3)*ell^(2/3)).

Weighted Cauchy–Schwarz gives |u-Nv|<exp(177ell) over that whole universe.
A finite Euler product gives only exp(o(ell)) positive first-ell-prime-smooth
integers below that bound. Each exponent vector and signed residual fixes
at most one N. Thus only exp(o(ell)) ell-bit N can have even one eligible
nonzero smooth residual in S_N. Zero can be included in the upper count;
it is not a smooth parity relation.

Verified primary Rosser–Schoenfeld prime-count inequalities give an ensemble
of Omega(2^ell/ell²) distinct squarefree semiprimes pq with
2^((ell-1)/2)<p<q<2^(ell/2). These inputs are coprime to the base eventually.
The fraction admitting any nonzero base-smooth residual is at most
exp(-(log 2)ell+o(ell)). For every sufficiently large ell, most members have
none, despite S_N being nonempty. This refutes H024 review item 7's proposed
all-large-composites inverse-polynomial smooth-density statement for the
specified generator. No random-smoothness heuristic is used.

## Limits and next action

This is an input-density upper bound and existence result. It does not give
an efficient algorithm producing the failing semiprimes, a useful numerical
threshold, an actual per-attempt rarity law for every fixed input/history,
or a new factoring algorithm. Exceptional inputs remain possible.

The alignment of primes with weights is essential to this output-width
proof. Weight permutations preserve the diagonal count but need not preserve
that width. Larger bases, higher energy, and N-dependent universes need new
arguments. A union over changed versions requires uniform bounds on each
version and on their number. No containment of a post-LLL correction domain
or perturbed tensor-network sampler was proved. No general logarithm-lattice
or factoring lower bound follows.

Close this precise supply route. Further work must propose a materially
changed mechanism that generates useful relations at a charged total cost;
mere escape from the theorem's assumptions is insufficient. Broader relation
generation and polynomial-sharing mechanisms are separate research questions.

No executable, finite experiment, benchmark, package or Lean file changed.
The prior successful shared checks remain the latest code validation; they
were not rerun for document-only mathematics. This review is not a Lean proof.

## Evidence identities

- Submitted draft: `2d0124e0b7fc46eb2e3e9d22c3520149272882a1b97f4289ff161b251e8a920f`.
- Hypothesis: `ff4f5cb565c6e38005a7586175ac1cecb4135b3478338b45a073d25ef429edea`.
- Review: `f5cec80695a1dcb6923987515fcea1fc47821bce4b72978113b0b323537c552d`.
- Archived primary PDF: `8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556`.
- Inspected page image: `c1faceab6e49fb9e526a07b876214fe8b0f326f822f3cbcb72745ba1ed9c9ad7`.

The completed T3 handle is retained in `research/tasks-H026.json`. Source
snapshots, review files and their manifest were not changed. The manifest's
STATE/report/disposition identities record their pre-acceptance versions;
subsequent coordinator checkpoint and acceptance edits are intentional.
