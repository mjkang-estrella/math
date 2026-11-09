# Verification and unverified matters

Symbolically checked in the report:

- Exact finite threshold representation and signed coincident-line weights.
- Primitive integer normalization, exact clipping, and constant contributions
  from empty, tangent or boundary-coincident threshold records.
- Horizontal/vertical orientations, parallel cases, corner endpoints and
  inside-only boundary samples without dividing by zero.
- Preservation of complete incident line lists under vertex deduplication.
- One original-floor initialization per walk, the self-weight relation,
  and signed atomic updates equal to the next actual offset's C value.
- Common intersection denominators at most 2B², midpoint denominators at
  most 8B⁴, and the sufficient offset delta=1/(64B⁶).
- Exact chamber coverage, empty-active-line handling and one-sided integer
  boundary representatives for the given nonnegative-normal floor formula.
- Proper gcd validation, repeated samples, every failed gcd and endpoints.
- Explicit intersection/sort/update counts, finite operand widths, imported
  acquisition/check costs, streaming workspace and additional output storage.

Accepted only at the stated interface:

- The old scalar-to-common-lift and large-base cover connections, supplied
  by the accepted review reports named in the assignment.
- Shared base acquisition and the fast-arithmetic model, including full
  denominator and unit eligibility checks. No nested evidence re-audit or
  new external arithmetic literature verification was performed.

Unverified or deliberately excluded:

- The new affine scalar/lift identity and actual affine witness claims.
- Any implementation of this edge walk, machine-model refinement, Lean
  theorem, measured runtime, or matched factoring benchmark.
- Useful-factor existence, positive success mass, independence, an N-only
  successful parameter schedule, or an improved factoring complexity bound.
- A repeat or extension of the terminal assay. Its two finite negatives
  and third setup-budget stop are existing observations only.
- Other live research, parent yield/order mechanisms, and follow-up reviews.

The command `sha256sum -c input-manifest.sha256.external` and then
`sha256sum -c input-manifest.sha256`, using project-relative paths, checks
the input freeze. The final delivery sidecar likewise anchors the delivery
manifest, whose entries can be verified with `sha256sum -c`. These are
administrative checks and execute no mathematical candidate. Delivery
manifest and its sidecar are the only excluded inventory files, to avoid
self-reference; every other owned payload and the review are included.
