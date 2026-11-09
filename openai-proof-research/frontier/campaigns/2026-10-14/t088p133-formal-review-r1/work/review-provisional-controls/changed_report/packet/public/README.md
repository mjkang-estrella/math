# T088P133 independent scoped formal review, round 1

Verdict **PASS_SCOPED_SUPPORT**, no required repairs. Read `review.md` for the exact statement, all 21 support/20 control audits, strictness and normalized use-site mapping; `limits.md` records actual reading, trust and preservation. This package grants no full-formalization, mathematical correctness, contribution, acceptance, count or release status.

The immutable implementation package must be supplied separately, matching all independently supplied hashes in anchors.json. The review does not redistribute its original mathematical scope/proof or private source bodies. `SemanticAudit.lean` adds 15 review declarations: eight exact interfaces and seven definition/use-site/boundary controls. All compile with standard axioms only. `exact_controls.py` checks rational examples and retained hypotheses using Python Fraction. `evidence/` contains the actual fresh build/type/axiom/control replay receipts, including both compiled assumption-mutation rejections. The original support/control audit log matches the sealed implementation byte for byte.

## Reproduce

Python 3, the companion immutable implementation at the original project path, trusted Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and the pinned precompiled mathlib/auxiliary cache are required. No network, Lake, git or dependency rebuild is used. Run from the review root, choosing a new output path:

```sh
python3 -B packet/public/replay.py --output "$PWD/work/fresh-replay" \
  --cache /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages \
  --lean /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
```

The initial recorded replay uses `--existing-build` to attach the first fresh build already performed in this session, rather than needlessly rerunning unchanged support. It still independently compiles the final review controls and both copied semantic mutations. Ordinary reproduction omits that option and extracts/builds a new package. Compiler products, generated drivers and temporary outputs stay in work/. All relevant dependency revisions are in evidence/receipt.json. Only project sources were rebuilt; precompiled dependencies are a disclosed trust assumption.

Use a **trusted copy** of verify.py against a candidate review package, supplying all three hashes from the independent handoff, not solely files read from that candidate:

```sh
python3 -B packet/public/verify.py --root "$PWD" \
  --final-sha256 EXTERNAL_FINAL_HASH \
  --manifest-sha256 EXTERNAL_MANIFEST_HASH \
  --report-sha256 EXTERNAL_OUTSIDE_REPORT_HASH \
  --originals /home/mj-kang/Documents/Dev/math/openai-proof-research
```

The optional originals argument checks the 1647 stable bindings and complete author/correctness-r3/formal root layouts. The two navigation/routing observations are excluded from preservation assertions. It does not add later parent files. Without originals, verification is portable artifact checking only. The verifier writes nothing.

`integrity_controls.py` takes the same three hashes and `--output "$PWD/work/review-tamper-new"`. It authenticates the review first, then tests clean acceptance and ten deliberate source/path/mode/link/anchor/reseal failures exclusively on new copies. It uses the review report as its payload target. These are integrity checks, separate from the semantic/type controls and formal analysis.

## Seal and exclusions

FINAL.json binds packet/MANIFEST.json and the outside REPORT.md. The manifest seals the exact packet path set, hashes/sizes/modes/link counts and directory metadata, excluding itself. FINAL, manifest and outside report must be ordinary mode-0644 single-link files. The exact portable set is FINAL.json, REPORT.md and packet/. work/ is excluded and not recursively authenticated by this seal; it contains failed experiments, original extraction, compiled products, copy-only controls and postseal receipts. All 56 formal declarations in the original+review sources were type/axiom audited; this does not formalize probability or geometry.

Original review prose © 2026 Myeongjin Kang (no affiliation), CC BY 4.0. Original code MIT. Adapted verifier/control scripts are from the same author's MIT implementation package; originals remain unchanged. See NOTICE.md and LICENSE-CODE.txt.
