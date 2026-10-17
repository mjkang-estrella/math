Independent scoped formal audit, S2 round 1.
Verdict and exact limitations: review.md and coverage-audit.json.
Author packet required at sibling seymour-s2-formal-r1, authenticated by
external manifest SHA dc95788a4e2d44c74c9c9a5d2a705641fc61baadc479cfe5903859911e01bc47.

Reproduce in this workspace (Linux bwrap, Python, pinned local Lean/cache):
  python3 -B audit.py --output .replays/unique-new-name
The output directory must not already exist. Every source build and generated
output stays under this review. External sources/cache are mounted read-only.
The portable author Lake configuration is tested with preprovisioned pinned
cache, not a network cache installation. See author README for standalone setup.

Canonical retained evidence is under evidence/: receipt, authentication,
complete logs and deliberately failing mutation sources with compiling
baselines. The *-false.lean files are negative tests, not project modules.
ReviewControls.lean is the independent positive test module. Author modules
remain byte-identical and external. Local run/, verified-run/ and .replays/
are generated scratch trees, excluded from the review payload; no compiled
objects, cache symlinks or third-party dependency files need distribution.

verify.py requires the externally reported review-manifest hash, verifies
listed contents and exact canonical payload membership, and authenticates
the original author's entire package without writing either package.
  python3 -B verify.py --anchor HASH_REPORTED_SEPARATELY
This checks identity, not truth. Fresh build evidence and source/type review
supply the scoped formal conclusion; full S2 remains unformalized.

Original review prose CC BY 4.0; original audit code MIT. Myeongjin Kang;
no affiliation. No publication or campaign acceptance claimed.
