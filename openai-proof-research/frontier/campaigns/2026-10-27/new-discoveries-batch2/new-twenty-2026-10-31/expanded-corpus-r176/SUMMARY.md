# Lane r176 research report

No eligible new candidate and no discovery credit. Exactly 20 ID-keyed dispositions are in results.json. This is a bounded investigation, not completion of the sixty-result campaign or a proof of the parked targets.

Nine targets have located public resolutions: 364985, 365076, 365077, 365295, 365523, 365579, 366341, 366405, 357395. The other eleven are parked with explicit gaps. The public proofs were read at the indicated statement/proof depth; external Lean developments were not replayed.

## Actual finite coverage

- Zero-sum groups: all 55 partitions of 16 for C2 x C3 x C3; six 2/3-part partitions for C4 x C3 x C3. Stronger inversion-symmetric certificates cover all part sizes for completed extension groups C4 x C3 x C3, C2 x C5 x C5, C2 x C3 x C9, C2 x C3 x C3 x C3, C8 x C3 x C3. The order-90 search reached the wall cap and was not restarted. Order 100 was not reached.
- Rainbow arborescences: 2 families at n=2 (exhaustive), 45 families at n=3 (exhaustive), 45760 families at n=4 (exhaustive), 20000 families at n=5 (random sample). No failure.
- Radial Moore degree 5: 13342464 switch proposals, 274602 valid evaluations, best 1426 versus conjectured 1445. Counts may include repeated graphs; heuristic only.
- Radial Moore degree 6: 11441602 switch proposals, 163981 valid evaluations, best 2980 versus conjectured 3126. Counts may include repeated graphs; heuristic only.
- Square embeddings on integer [-3,3]^2: 2193360 assignments; 21960 pass edge constraints; 8 pass local cones; 0 nonisometric.

## Reproducibility and limitations

Run scripts/limited.py NAME python3 -I scripts/SCRIPT.py ARGS from the lane (use absolute script paths if elsewhere). One heavy process at a time. Receipts retain sampled process-group RSS, 2-CPU affinity, CPU 120 s, wall 140 s and exit state; environment sets MALLOC_ARENA_MAX=2. No Lean was invoked. A C++ prototype was not compiled because g++ is unavailable; the executed radial searches use Python. Initial oversized Omega root tree is a truncated local response and was not treated as complete; complete D5 and Problems subtrees replace it. Eight GitHub repository queries were spaced eight seconds. All listed arXiv versions were downloaded, but body review is selective and explicitly recorded. No universal novelty clearance or complete technical review is claimed.

The source statement hashes and exact raw newline-preserving corpus rows are preserved in raw/, extracted.json and results.json. HTTP receipts are in outputs/fetch-*.json; registry heads, queries, hits and limits in outputs/registry-screen.json. Mathematical mechanisms and known-resolution bridges are in outputs/MATHEMATICAL-NOTES.md.

CANDIDATE.md records the negative nomination decision. No Lean packet is fabricated: there is no new eligible theorem to certify. No git, shared ledger/index edit, child agent, browser tab, upload, author contact or external message was used. No campaign count changed.

Procedural limitation: the complete Lean Pool code tree and candidates metadata were screened before the numerical routes, but its projects manifest was corrected and screened afterward. The brief names root projects.yml (404); the actual file is LeanPool/projects.yml. This is recorded in the registry report. This pass also did not constitute the several-hour sustained investigation envisaged by the brief; parked entries are explicit unfinished routes, not completed resolutions.
