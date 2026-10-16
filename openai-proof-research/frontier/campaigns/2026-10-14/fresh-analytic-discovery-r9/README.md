# Fresh analytic discovery r9 — private research handoff

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.

Status: **PROPOSED_COMPLETE_PENDING_INDEPENDENT_GATES**, full frozen G.
Campaign remains **4/10**. Nothing accepted, counted, published, submitted or
formalized here. F's existing proof PASS / contribution TECHNICAL remains
unchanged, with both reviews and parent corrections preserved.

* original-scope.md: exact full target, frozen before proof work.
* candidate.md: proposed complete proof, exact constants/operator/domain,
  bounded predecessor comparison and computational limitations.
* source-contracts.md and literature-screen.md: actual reading extents and
  primary-source comparison, without worldwide novelty claims.
* working-math.md and progress.md: incremental mathematics and chronology.
* review-brief.md: full-scope independent proof/contribution questions.
* inputs/private/: preserved inputs and third-party private reading copies.
* checks.py / checks-receipt.json: exact finite support only.
* inputs-manifest.json / outputs-manifest.json: exact SHA256/size inventories.
* seal.json / seal.sha256: inventories' seal and detached convenience copy.

Authenticate seal.json against the externally delivered SHA256 first, then:

    python -B verify.py EXTERNAL_SEAL_SHA256

verify.py authenticates payloads, membership, frozen scope, preserved F and
13 pinned Git blobs before replaying only checks.py. It does not write,
regenerate receipts or execute preserved third-party/predecessor code.
The external terminal hash is the root of trust; seal.sha256 alone is not.
Rights are in RIGHTS.md. The parent alone integrates and commissions gates.
