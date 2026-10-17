CDF098 scoped Lean support — Myeongjin Kang, no affiliation
Original prose CC BY 4.0; original code MIT (LICENSE.txt).

This package proves finite metric-cover, recentering, transfer, packing,
dyadic-cardinality, normed-segment and distance/count lemmas used by the
frozen CDF098 proof. It does not formalize the full universal Banach-curve
theorem. See coverage.json for an exhaustive theorem/interface map and the
remaining geometric, topological and source inputs. The full target is not
replaced by a partial claim. There is no count or acceptance change.

CDFLocal.lean: 30 support theorems and 9 definitions.
Controls.lean: 11 exact instances and false-variant witnesses.
Checks.lean / ControlChecks.lean print every public type and every axiom
dependency. Only propext, Classical.choice and Quot.sound occur. There are
no new axioms, sorry/admit, unsafe declarations or native_decide. Statements
use actual metric distances and finite centers. DoublingBound is explicitly
defined by closed balls with centers in the metric type; subtype spaces
therefore use centers in that subset. No graph-path metric is substituted.

The implementation agent previously authored cdf098-contribution-r1.
This implementation and its checks are NOT an independent formal audit.
A separate formal reviewer must evaluate the exact package. The previous
full-proof and contribution records are authenticated contextual inputs,
not automatically a verdict on these new Lean files.

Pinned environment:
  Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52
  mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
  nine package revisions in lake-manifest.json
The established cache is read-only. Existing dependency objects, compiler,
standard library and runtime are explicit trusted inputs. Their source
revisions and tracked-tree cleanliness were checked, and compiler binary
SHA256 was recorded; the caches were not rebuilt or fully byte-authenticated.
No source-to-binary reproducibility or compiler-signature claim is made.

Read-only identity verification:
  python -B /path/to/package/verify.py --anchor EXTERNAL_OUTPUT_MANIFEST_SHA256
Optionally add --check-inputs to recheck the original campaign inputs in
place. Snapshot inputs are checked by default. The caller must supply the
manifest hash independently; the script checks it before parsing and checks
exact file and directory membership, sizes, hashes, input anchors, source/
build linkage and logged controls. It does not reprove mathematics.

Fresh source reproduction:
  python -B /path/to/package/rebuild.py
  python -B /path/to/package/mutations.py
Optional --cache PATH and --lean PATH select installations with the exact
pinned versions. Default output is a new .replays/TIMESTAMP directory inside
this package, excluded from the original seal. Each build copies the four
current Lean sources into a fresh temporary directory, compiles the support
and controls there, reads their new objects for type/axiom checks, and then
deletes temporary objects. It never uses older CDFLocal or Controls objects.
Both retained successful builds use the same final source. Their complete
type and axiom outputs are identical. No .olean is part of this package.

Six false variants must fail at proof goals: recentering without factor two;
weak instead of strict packing separation; one extra power in the dyadic
window width; too-small fine-edge radius; too-large cluster-separation
constant; and low-count coefficient 80 instead of 81. Import/parser/name/type
errors are invalid negative controls. The retained logs show ring, linarith
or omega proof failures; exact counterexamples are in Controls.lean and the
bounded semantic diagnostics. A real wrapper invocation printing SOME FAIL
while exiting zero was also rejected. Numeric diagnostics are not universal
proofs or substitutes for the missing geometric construction.

The finite graph, all case-cover assembly, Hilbert product identifications,
source witnesses, Dvoretzky existence, infinite cluster assembly, tours,
compactness, Lipschitz parametrization and final nonembedding argument remain
outside Lean. In particular graph_count assumes a cover-count inequality;
it does not establish that the constructed graph has such a cover.
