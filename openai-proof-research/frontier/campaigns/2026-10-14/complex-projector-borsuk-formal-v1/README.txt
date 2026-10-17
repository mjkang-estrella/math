B8C scoped formal support — Myeongjin Kang, no affiliation
Original prose: CC BY 4.0. Original code: MIT (LICENSE.txt).

This package certifies the local scalar two-trio argument and exact complex
score expansion in the frozen B8C proof. It DOES NOT formalize the full
CP2/Hermitian/topological theorem. coverage.json maps every theorem to its
precise interface and lists the geometric and analytic parts still external.
No acceptance, contribution verdict, full-theorem formal PASS or count change.

BorsukLocal.lean has 16 support theorems and three definitions.
Controls.lean has 13 exact positive instances / negative-variant witnesses.
Checks.lean and ControlChecks.lean print every public declaration's type
and axioms. The only admitted kernel axioms are propext, Classical.choice
and Quot.sound; no source theorem is introduced as a new axiom. No sorry,
admit, unsafe or native_decide is used.

Pinned environment:
  Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52
  mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
  all nine package revisions: lake-manifest.json
The established campaign dependency cache is reused read-only. Original
runner/config provenance is in provenance.json. No original manuscript,
source, review, shared ledger, dependency cache, or other project is edited.

Verification (from any directory):
  python -B /path/to/this/verify.py --anchor EXTERNALLY_SUPPLIED_MANIFEST_SHA256
Add --check-inputs to verify the fixed external campaign files in place.
The externally supplied hash must match output-manifest.json BEFORE parsing.
The verifier checks exact sealed membership, bytes and build/source linkage.
It is an integrity verifier, not a new mathematical proof or novelty check.

Fresh rebuild:
  python -B /path/to/this/rebuild.py
  python -B /path/to/this/mutations.py
Optional --lean PATH and --cache PATH use another installation with exactly
the pinned compiler and dependency revisions. Both scripts check the pins.
They write only new subdirectories within this package; default output is
.replays/TIMESTAMP, explicitly outside the sealed payload. Each rebuild
copies the FOUR current Lean source files into a new temporary directory,
compiles the support and controls from scratch, checks all exact types and
axioms, rejects any compiler warning or failure-marker output, runs the
exact rational controls, and deletes temporary .olean files. It never uses
an earlier support .olean. The pinned mathlib .olean cache is an explicit
trusted dependency, not rebuilt here. Normal Lake configuration is also
provided for separately provisioning the pinned dependencies.

The retained first-build and clean-rebuild logs are two fresh runs of the
same source. Five mutation checks must fail at mathematical proof goals:
wrong favored margin, excessive epsilon allowance, wrong other-trio margin,
non-strict cap margin, and omission of the complex conjugate. Import/parser/
unknown-name/type errors are rejected as invalid negative controls. Exact
counterexamples are recorded in Controls.lean and semantic_checks.py.

The finite rational diagnostics exercise all three branches and chart
instances; they are NOT a proof for all parameters. The Lean theorem is the
universal proof. The CP2 theorem remains supported by its separate human
proof/review and must not be described as fully formalized by this package.
