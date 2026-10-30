# r36: unresolved; credit 0

Screened AIM617/509/611 and selected AIM503 / clopen OP-00880: for every n>=6, is the labelled leaf-slide graph diameter floor(n²/2)-n? Oswald568 was excluded as prior r33 effort. Read actual published Kozlov2025 OpenQuestion2.5, current2607.07404v1 upper/lower-bound proof bodies, matching-complex conjecture/theorem and cospherical conjecture. No full source resolution found.

Tested edge-split transport. Its cost/assignment construction is classical: actual Bogdanowicz2011 publisher PDF Definitions2.1/4.1 and Theorem2.2 read. Proved this lower bound is insufficient in ALL orders n>=9: any diametral pair must be paths by source equality conditions, but path split transport is <=3n²/8<floor(n²/2)-n. This is a failed-route obstruction, not a new credited theorem or source refutation.

Exact capped checker traverses all125/1296/16807 trees from one path at n5/6/7, all60/360/2520 labelled path targets modulo reversal, and6480 directed split updates at n5/6. True path eccentricities6/12/17; max path transport6/10/14. Explicit n6 distance12 vs transport8 falsifies equality of the metrics. Closed-form obstruction sums checked through m1000. `bash run-checks.sh` passes under512MiBAS/40CPU/55wall/BLAS1. Finite cases only corroborate the obstruction, not the full conjecture.

Live Omega dev50b390046e2079f4215f0e88ab3b344f6a40fd3f, latest11:38:53UTC;79commit/155file reported delta from cf6f598 reconciled with inherited complete D5/Problems inventories. Other four heads unchanged. No whole-dev or noveltyPASS. Current arXiv history lists only v1; author group page is not a bibliography, so followup coverage remains bounded. Exact URLs/UTC/hashes/failures retained.

No candidate PROOF.md, Lean, paper, acceptance or count change. Root owns acceptance;5additional/35total unchanged. All writes confined to this lane; no children, git, external mutations or browser tabs. See discovery.md, FAILED-ROUTES.md, provenance.json and manifest.json.
