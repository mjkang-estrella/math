# T117Q scoped spectral-selector support

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT.
This is frozen author-side implementation support, not an independent proof review,
contribution decision, campaign acceptance, or formalization of full T117Q.
The frozen structural r59 packet is unchanged.

`T117Q.lean` proves the finite-dimensional spectral-selector and positive-trace
core used in candidate.md §3. Its matrix inequalities use mathlib's Loewner
order, never entrywise order. The index of the matrices is any finite type
(including the empty type); the family is any finite set. Scalars are real
and matrices complex. There are no commutation assumptions between selectors,
between different input matrices, or between a selector and the positive
trace-pairing matrix.

For each positive semidefinite Q, `spectralCut Q hQ h` constructs the spectral
projection P onto eigenvalues at most h, using mathlib's Hermitian spectral
theorem. The construction proves positivity, P ≤ I, idempotence,
h(I−P) ≤ Q, and PQP ≤ hP. `spectralCut_domination` additionally derives
P(Z*Z)P ≤ hP from Z*Z ≤ Q, for arbitrary complex Z. It does not take the
projection, defect estimate or compression estimate as an assumption.

For h > 0 and a finite family with

    sum Q_s ≤ (h * number_of_charts / 2) I,

`spectral_half_coverage` proves

    (number_of_charts / 2) I ≤ sum spectralCut(Q_s).

`trace_product_nonneg` proves Re Tr(AB) ≥ 0 for positive A,B by factoring
A=C^* C and cyclically moving factors to the positive matrix CBC^*. This
justifies the noncommuting positive pairing. `spectral_trace_bound` combines
the constructed selectors and coverage to prove

    (number_of_charts / 2) Re Tr(Y) ≤ sum Re Tr(Y P_s)

for positive Y. Finally, `trace_budget_consequence` proves Re Tr(Y) ≤ 2b
when the family is nonempty and every chart contribution is at most b.
In T117Q §3 the intended substitution is b=Nt sqrt(h)+e. The actual upper
bound on each chart is an unformalized input, not a conclusion of this file.

The mathematical connection is direct: Q_s=(sum_i Z_si^(2q))^(1/q) and
h=8 exp(1) q/m in the candidate. The Lean development does not construct
those fractional powers or establish their input budget. It formalizes the
subsequent finite selector deduction for every family satisfying that budget.

Unformalized parts include the Gaussian/Wick register contraction and moment
integrals; the finite universal empirical moment construction; operator
concavity and Loewner–Heinz used to obtain Q_s and Z_si² ≤ Q_s; conversion of
the compressed-square bound into the operator-norm estimate; the Bessel and
Gaussian-sign construction of Y; trace-norm duality and the chart error
estimate; all pinned-source kernel/triangle-repair/metric/coarea geometry;
the uniform-copy procedure, asymptotics and infinite-dimensional trace-class
passage. In particular, neither T117Q's metric nor its full distortion theorem
is represented by a Lean declaration here.

`Controls.lean` contains two explicit positive rank-one projections that do
not commute, and applies the positive trace lemma to them. It proves that
positive pairing fails without positivity of Y; that the abstract defect-to-
coverage implication can fail at h=0; and that cancellation of family size
cannot omit nonemptiness. It also checks, for every finite matrix size and
unitary spectral model, that eigenvalues equal to the threshold are retained
and eigenvalues strictly above it are discarded. These are kernel-checked
hypothesis controls, not floating-point tests. The zero-threshold example is
for the abstract `selector_coverage` interface; it does not assert failure
for genuine spectral cutoffs of a zero PSD matrix.

`rebuild.py` is adapted from the T205M author-side support builder, with module
names changed. Its provenance and input identities are in provenance.json.
It verifies Lean 4.34.1 and all nine dependency revisions, including mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and checks tracked dependency
cleanliness. It compiles fresh local objects outside this packet, prints the
full type of each public definition and theorem, and audits all corresponding
axiom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed. The pinned dependency object cache is trusted and is not rebuilt.
The builder and its audit are not an independent mathematical review.

Run from any directory with a new, unused output path:

```text
python3 -B /absolute/path/to/t117q-formal-v1/rebuild.py --output /var/tmp/NEW-T117Q-BUILD
```

`--cache` and `--lean` override local installation paths with the same pin
checks. Builds never create package-local .olean or .lake files. The final
successful logs, declaration audit and source hashes are copied to validation/.
Earlier failed control builds are retained in development-failures/; they
were type/proof-script errors, not ignored successes. probe.py is a development
helper; rebuild.py is the authoritative build and audit command.

The parent froze this review packet from development inventory SHA256
`0be6379a252f737fb91b6da64691266861631e3f2c15de6d24e28305aa5981a6`. Its original inventory.json is retained as provenance, not as the
external anchor of this enlarged packet. Authenticate manifest.json against
the external parent-dispatched SHA256 using verify.py --anchor HASH.
Integrity controls use /var/tmp copies only. Parent source review and
packaging are not independent formal review.
