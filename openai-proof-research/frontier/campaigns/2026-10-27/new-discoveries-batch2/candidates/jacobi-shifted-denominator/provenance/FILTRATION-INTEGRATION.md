# Binary filtration integrated

Root inspected all four proof sources and all 54 actual type/axiom reports, and
compiled the copied sources in a new isolated directory with no preexisting
local oleans. All five builds (four proof modules and exhaustive audit) exited
zero under warnings-as-errors. Proof-module logs are empty. All declarations
use only the permitted three axioms; additive_nat_mul uses none.

The original four proof modules are byte-identical in formal/. Only the audit
filename changes to FiltrationAudit.lean. Original and integrated source hashes
are recorded in filtration-import-map.json. The fresh build receipt is
filtration-root-replay.json, with actual logs in verification/filtration-root-fresh/.
The implementation lane remains untouched. Its reported historical T3 thread
could not be retrieved (thread_not_found); this adoption rests on inspected
on-disk sources and the root's own build, not a claimed thread read.

The arithmetic class is over an arbitrary commutative coefficient ring and
requires zero parameter-constant coefficient. Binary subadditivity is derived
from the exact factorial valuation identity with subtraction bounds. Actual
polynomial expansion proves 2fg and square closure; finite involution induction
separately proves the spectral convolution pairing. The coefficient additive
map preserves powers of two by map_nsmul. The resulting recurrence theorem has
only genuine initial-value and recurrence premises. The integer negative
control proves the class is not a subring. No rational-ring divisibility shortcut
or assumed square/convolution closure is used.

An initial root report-parser assertion counted only 53 axiom-dependent reports,
missing the single axiom-free report. The Lean builds themselves all passed.
The corrected parser records all 54; no source correction or recompile was needed.

Complete component only: the concrete midpoint algebra/derivation and source
sequence must still be constructed, its parity/primitive properties proved,
and the literal source logarithm connected to it. Catalan attainment assembly,
the closed SourceClaim, manuscript, independent final review, and extracted
final packet remain. Candidate credit 0; accepted count 32/60 unchanged.
