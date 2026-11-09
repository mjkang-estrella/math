Unconditional source refutation, formal PASS; no acceptance/count/priority claim.

Exact endpoint: FourAttractor.source_refuted : ¬ FourAttractor.SourceClaim.
SourceClaim is literally ∀ d t : Nat → Bool, ∀ n, ∃ g : Finset (Fin
(prefixWord d t n).length), Attractor (prefixWord d t n) g ∧ g.card ≤ 4.
No closure, admissibility, occurrence-array, or hitting-set premise remains.
The Attractor definition quantifies every nonempty factor with an occurrence,
then requires some occurrence crossing a selected position.

Closure.lean proves reversal/exchange involution and antimorphism laws, the
reflected extension identity for extensions no longer than the input, existence
of a full-length candidate, and least-length closure among ALL fixed extensions.
Longer extensions are bounded separately; closure_unique proves uniqueness.
Words.lean kernel-checks the five least candidate lengths 1,1,5,7,17,
equivalent to longest suffix lengths 0,2,0,4,2. It proves fifth=w for
w=010110010101100101101001101010011010. Explicit infinite directives use
00101 followed by zeros, EEEER followed by Rs. No aperiodicity is required.
prefix_step, strict_growth, length_ge, prefix_nested, infiniteWord,
prefixes_infinite and definition3 construct the actual infinite sequence.
All finite defining words prefix it and their lengths tend to infinity.

Attractor.lean kernel-checks all starts 0..36 for eleven literal factors;
the length bound reduces any possible occurrence to this range. Each necessary
coverage lemma is derived from the full Attractor predicate. Geometry.lean
proves a generic interval impossibility for arbitrary four natural positions
with omega (about 11 seconds), rather than enumerating 58,905 four-subsets.
coverFour pads lists of length ≤4 by repetitions; consequently no assumption
of exactly four distinct positions or of positions lying in the three blocks
is hidden. Endpoint.lean proves no_four, source_refuted and intrinsic_witness.
The latter also gives palindrome status, the infinite-prefix bridge, and the
strict lower bound for every attractor of w. No all-n optimum, sharp family
bound, minimal counterexample length, or size-five upper bound is claimed.

Five mathematical modules; final inventory 120 actual owned declarations,
including private/generated/instances: Closure30, Words28, Geometry5,
Attractor50, Endpoint7. All actual types/origins/safety and transitive axioms
are printed in Audit.log. Only propext, Classical.choice, Quot.sound occur;
no unsafe or partial owned declarations survive. The initially generated
partial prefixWord helper was eliminated with explicit Nat.rec.

RUN performs strict serial compilation/audit, verifies the compiler and all
nine package pins, and checks original/copy scientific hashes before/after.
source-only.zip has fixed member ordering/timestamps/permissions and no owned
compiled artifacts. A fresh extraction into fresh-replay is replayed by RUN;
its logs, guard receipts and audit receipt are delivered separately. Final
manifest.json excludes itself and verification-receipt.json. The latter is
created only by a separate guarded invocation after final writes.

Residuals: no mathematical/formal premise remains at the endpoint. Novelty
and independent final review remain root's responsibility; preliminary
review's bounded novelty HOLD and inaccessible registry intervals persist.
No manuscript, public/shared/git/MathDB edit or acceptance/count change.
Counts remain 9 additional / 39 total / next40; root alone decides.
