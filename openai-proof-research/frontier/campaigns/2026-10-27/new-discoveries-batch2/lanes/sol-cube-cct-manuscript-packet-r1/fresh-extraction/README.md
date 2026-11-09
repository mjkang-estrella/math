# Cube CCT manuscript source packet

Status: mathematical/formal n=5 PASS; PDF BLOCKED; novelty/acceptance HOLD.
The manuscript is designed as four pages, separated by `---PAGE---`. No PDF
was authored: the mandatory PDF marker crashed twice under AS512MiB with
`SegmentedTable::InitializeTable (subspace allocation)`, even with legitimate
`--jitless --max-old-space-size=64` flags. No cap increase or marker bypass
was attempted. Page count/layout and PDF byte reproducibility are UNVERIFIED.

`manuscript.md` is the complete readable paper. `build_pdf.py` is its unexecuted
ReportLab renderer with invariant PDF timestamps. It is offered as source,
not as a successfully tested PDF build. Before PDF authoring, run the PDF
skill's mandatory marker successfully exactly once immediately before the
first authoring command; then run `build_pdf.py`, render every page with
Poppler and visually inspect every page. Do not claim PDF QA until performed.

## Immutable formal component

The original `formal/` source members are byte unchanged from archive SHA256
ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d.
No own compiled artifacts are included. `formal/run.sh` is the original runner
for the pinned campaign installation. `portable_replay.py` adds a relocatable
runner: set CUBE_LEAN to the compiler executable and CUBE_PACKAGES to the
directory of the nine pinned package checkouts. Their local library oleans
must already exist. Set CUBE_LAKE_MANIFEST to the pinned Lake manifest.
This does not fetch dependencies or rebuild/authenticate all library oleans.

Execute the replay driver itself directly (it is the dedicated fixed Lean
runner), with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1.
It fixes serial Lean -j1 -M2700, group RSS2800MiB CPU210 wall230 for each
compiler call. It runs ordinary pin/audit work through the supplied helper
guard at AS/group RSS512MiB CPU210 wall230. Do not run the Lean driver inside
the helper AS512MiB process. All helpers below MUST run through helper_guard.py.

Fresh replay: `python3 portable_replay.py` (dedicated Lean exception).
Audit only: `python3 helper_guard.py python3 audit_packet.py`.
Finite reproduction: `python3 helper_guard.py python3 reproduce.py`.
ZIP rebuild: `python3 helper_guard.py python3 rebuild_zip.py /path/to/source-only.zip`.
The ZIP writer stores sorted source paths with fixed 1980 timestamp and 0644
permissions, excludes generated replay/output files, and uses no compression.
Re-extract the ZIP into an empty directory and run that same ZIP writer there:
the resulting bytes must match. `package-files.json` fixes all archive members
except itself (which is included in the ZIP). No ledger or NEXT live bindings
are used by any build. Administrative snapshots remain outside the package.

## Evidence and boundaries

`evidence/` contains the inspected primary bodies and retrieval receipts,
reviews, source summary and this lane's complete fresh strict audit/logs.
PROVENANCE.json binds the larger frozen evidence to original paths and hashes;
these are historical references, not dependencies on mutable administrative
state. The final lane manifest/receipt are separate from the ZIP.

Counts remain 9 additional / 39 total / next 40. Root alone accepts/counts.
No priority clearance, acceptance, minimum witness, n<5 classification,
universal formal n>=5 claim, or Conjecture 1.3 refutation is asserted.
