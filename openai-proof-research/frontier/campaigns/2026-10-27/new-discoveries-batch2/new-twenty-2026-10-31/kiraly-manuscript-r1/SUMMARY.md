# Candidate 388087 draft manuscript and reproducible packet

Prepared 2026-10-31 America/Los_Angeles (2026-11-01 UTC). DRAFT only: no acceptance,
count change, submission, publication or external contact. Work is confined to
kiraly-manuscript-r1; all frozen theorem bytes are unchanged.

Deliverables:

- `paper/manuscript.pdf`: seven-page compiled and visually inspected manuscript.
- `paper/manuscript.tex`: complete LaTeX source, bibliography and witness table.
- `proof-packet.zip`: portable theorem/replay archive, freshly extracted and tested.
- `packet/`: unpacked identical packet, including nine-package pinned manifest.
- `source-to-paper.json`: exact primary versions, URLs, hashes and theorem mapping.
- `sources/`: primary bodies actually used and completed independent reviews.
- `logs/`: input bindings, exact data checks, build/render logs and final replay.
- `results.json`, `metadata.json`, `MANIFEST.sha256`: machine-readable status/hashes.
- `kiraly-draft-dossier.zip`: compact paper + packet + sources/logs/metadata dossier;
  excludes tool caches, binaries, dependency trees and rebuilt theorem objects.

Theorem: the eleven displayed triple edges form a nonideal clutter with a genuine
real fractional extreme point at (1/3,...,1/3), yet admit no Kiraly choice maps on
the clutter and its full blocker. A 6,517-leaf literal certificate is checked in
Lean by a proved-sound finite checker. All 36 listed minimal-transversal memberships
are used. Whole-blocker equality, mni and canonical catalogue classification are
not needed formal claims. The JSON `core` field denotes the full unsatisfiable
constraint collection, not a Lehman minimum-edge core.

The manuscript supplies the linear elimination, all minimal-transversal witnesses,
checker specification and soundness argument, exact endpoint references, and an
explicit mate identity. A supplemental ordinary derivation of the blocker's
fractional vertex addresses the literal "both families nonideal" premise of Pap's
January 2011 revision/thesis; it is not a new Lean theorem or credited outcome.

Final extracted replay: strict Lean compile PASS (13.764 s), warningAsError=true,
two threads/CPU affinity, both endpoint axiom lists exactly propext,
Classical.choice, Quot.sound; optional module leanchecker PASS. The original
file hash is 1370129f56ef40e2dc317a8cf12ef8d7ed1a0e77eb4d6374d182ee9d4ddcddbb.
The packet script constructs LEAN_PATH from a configurable dependency root.

Trust and limitations:

- Uses existing prebuilt pinned external packages; no fresh network-source
  Lean/mathlib build. Checkout revisions are verified, but the full transitive
  object closure is not authenticated by content hashes. Selected fingerprints
  are recorded separately. Dependencies are read-only by convention/user-writable.
- Cli checkout exists but has no built library; unused path is omitted and logged.
- leanchecker verifies the new module against imports, without --fresh full mathlib.
- Completed fidelity review: PASS. Completed significance review: qualified
  bounded-prior PASS. Their copied reports preserve provenance and independence;
  neither reviewed this finished paper or gives this investigator acceptance authority.
- The underlying object is known. Assessed contribution is the all-choices
  full-blocker obstruction, not a new matrix, minimality or formalization alone.
  The original Lutolf-Margot catalogue remains unread; later-literature coverage
  is incomplete. No worldwide-priority claim or chronological subsumption shortcut.
- No fresh independent literature search was duplicated by this preparation lane.
  Review receipts support their stated bounded screen, not universal clearance.
- Initial packaging/build attempts and their failures are preserved in logs;
  final logs identify the corrected successful run. No mathematical proof repair.

PDF build used Tectonic 0.17.0, downloaded locally from its public release, with a
copied existing TeX cache to avoid redundant fetching. Final compile has no TeX
warnings. Pages were rendered with pdftoppm and inspected as a contact sheet and
selected full-size pages; no clipping or overlap was observed. Build tool/cache
is excluded from the portable dossier. `tools/build-paper.sh` accepts TECTONIC.

Parent integration and final paper review remain outstanding. Accepted credit: 0.
