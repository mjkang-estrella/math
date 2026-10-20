# T106O133 contribution review r1: TECHNICAL (conditional on correctness)

This is the first independent contribution review of the frozen nominee T106O133 (structural r133, family 106). Reviewer: Factory Droid / claude-opus-5-5. Pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, stipulated true. No correctness gate, acceptance or count is assigned here. The full review is in [packet/public/review.md](packet/public/review.md), and the machine-readable verdict is in [packet/public/verdict.json](packet/public/verdict.json).

**Scope assessed (unchanged).**

- Theorem A: for every fixed k >= 1 and delta > 0, there is a deterministic polynomial-time reduction from 3SAT to nonempty simple graphs that are C_{2k+1}-colourable when the formula is satisfiable, and have independence ratio below delta when it is not.
- Corollary B: the full Brakensiek-Guruswami conjecture (KOWZ Conjecture 1.2), with its decision, search and density forms.

The frozen statement (SHA256 72654d28…1256) and proof (eb3ea4c6…a32c) were authenticated against the detached parent anchors before use.

**Verdict: TECHNICAL.**

- Source 106's operative soundness proof consumes its hardcoded threshold 1/8 only through an explicit interface: f is odd, [-1,1]-valued, equal to 1 on the independent set, constant on zero links, and L-Lipschitz. After that it uses only the symbol L. Its analytic lemmas hold for every finite L, and every constant is chosen after L.
- The nominee substitutes 1/(4k+2) for the threshold and 8k+4 for L. Its arc colouring is the folklore fact that chi_c <= 2 + 1/k iff G -> C_{2k+1}, recorded in KOWZ and applied to source 106's own phase map. Corollary B is the standard sandwich and fibre count.
- I found no nonroutine compatibility step.
- The consequence is significant. arXiv 2605.09815v2 (18 Oct 2026) still called BG known only under the Rich 2-to-1 Conjecture, and it does not cite source 106. But the significance lies in a corollary of the stipulated source method, and the project rule excludes routine transfers.

**Not REDISCOVERED; priority unresolved.**

- No prior statement was found in source 106, pinned 105 or 102, BBN v2, FMW (the original ECCC and revision 2), KOWZ, the original BG paper, or bounded web searches.
- The FMW Remark 1.13 supplement could not be located. It is absent from ECCC revision 2, and it is unread.

**Rich 2-to-1 test.**

- BBN's richness requires each left vertex's incident maps to be uniform over all 2-to-1 maps, with perfect completeness.
- Pinned 105 is ordinary 2-to-1 and explicitly disclaims richness. Its edge maps pair legal labels only along one kernel vector, and its completion step fixes legal images.
- Pinned 102 has completeness 1 - epsilon.
- So the BBN conditional route is not paid by the pin.

**Unresolved issues and limits.**

- Worldwide priority is open, and the FMW supplement is unread.
- I did not read the BKLM, Avvakumov et al. or Wrochna-Zivny full texts.
- Source 105 was read only at its introduction, construction-edge and completion windows.
- No proof blocker was found, but this is not a correctness review.
- Exact extents are in [packet/public/reading-limits.md](packet/public/reading-limits.md); rights are in [packet/public/rights.md](packet/public/rights.md).

**Disclosures.**

- All of my own writes are inside this root.
- Harness tooling stored some command and fetch outputs outside it (/tmp and the tool-output cache).
- The parent directory changed during the review through parent activity. I did not read the changed parent files. Only the two parent inputs I used are pinned.
- No author, parent, shared-index or git changes. No nested agents, browser UI, upload, contact, publication, formal or manuscript work.

**Seal.**

Packet MANIFEST SHA256: `9a795f7876886c5385618226c8434ee6c9a29f49c33a0472534229abe1510143`
review.md SHA256: `d71c113f743fadfdd5e6c42fcd4a7881d6736441175181637c72542a6bccf097`
verdict.json SHA256: `cf178fd7a09ee50fdd60b2545d216d6260b685a6cee4331b2b65dd2369a3feea`
input-fingerprints.json SHA256: `ed95191e2d1783ec4a81f0ae1341253c449e8cf92bdfdb8cad62197f8d4fa794`

FINAL.json binds this report, the manifest, the review, the verdict and the input fingerprints. Its SHA256 is supplied detached, in the reviewer's handoff. Verification is read-only and requires both detached anchors:

    python -B packet/public/verify.py --root . --project /home/mj-kang/Documents/Dev/math/openai-proof-research --finalhash DETACHED_FINAL_SHA256 --author-finalhash 28c1114b783e345e666741df7eadeecccdf6ae92aff898adf4a778b06624d832

The copied controls run only on copies inside this root. Their receipt, `artifact-controls.json`, lies outside the packet and is not bound by FINAL:

    python -B packet/public/controls.py --root . --project /home/mj-kang/Documents/Dev/math/openai-proof-research --finalhash DETACHED_FINAL_SHA256 --author-finalhash 28c1114b783e345e666741df7eadeecccdf6ae92aff898adf4a778b06624d832

Artifact checks are not mathematical or contribution judgments.
