# progress.md — pi-bbk-full-refinement-r3

## Timeline (UTC)

- **2026-10-28 17:31** Lane created; prior-art screen (MathDB live check, arXiv v1 fetch, 5 citers' bodies) closed first.
- **2026-10-28 (late)** `run1_identities.py`: symmetry G_{k,n}=G_{n+1,k−1} + canonical reduction verified (k,n ≤ 10, N=300); simple-pole lemma e_c ∈ {−1,0,1} for k,n ≤ 40. Naive lcm-period scan hung (exponential expansion) — restructured.
- **2026-10-28/29** `run2_subobjects.py`: (a) sub-object (1−q⁷)/((1−q³)(1−q⁵)) negative at q⁷ — kills sub-object induction; (b) h-superadditivity verified u ≤ 400; (c) divisor-matching fails at 229 (M,m) pairs.
- **2026-10-29 03:00–04:00** `run3_k4_scan.py`: wide k=4 sanity (n < 2000, full m-range for n ≤ ~450) — clean. **Fixed a bug in the direct-series check** (product tails beyond the truncated inverse are invalid; earlier "G_{4,2} min = −5640" was this bug, not a fact).
- **2026-10-29 04:00** `run4_k4_proof.py`: **complete k=4 machine** — 15 D-classes + 225 tail classes, all Newton data ≥ 0 → **Theorem A**. Prop 2.2 verified vs series (all r, Q ≤ 20).
- **2026-10-29 04:05** `run5_k5_probe.py`: k=5 clean numerically (n < 200 tail + full initial range for n < 200).
- **2026-10-29 04:10** `run6_k5_proof.py`: cubic data (105 residues) verified; tail-quadrant certificate: **0 failures over 11025 classes**. Initial regimes failed the naive quadrant test — diagnosed as domain mismatch (quadrant ⊋ regime).
- **2026-10-29 04:20** `run7_k5_regimes.py`: regime-exact certificates — slabs (B5/B6) + wedges (B4/B7): **0 failures**; regime formulas cross-checked vs unconditional T₅.
- **2026-10-29 04:25** `run8_k5_close.py`: R1/R2 slabs 0 failures; **loop closure: T₅ vs direct series 27 009/27 009** → **Theorem B**.
- **2026-10-29 04:30** `run9_k6_probe.py`: k=6 tail, 225-class sample — 0 failures (compute wall, not math wall).
- **2026-10-29 04:35–04:50** Lean toolchain verified; `lean/Bridge.lean` compiles (statements only); all documents written.

## Status

**Deliverables complete:** PROOF-K4-K5.md (main), SUMMARY.md, discovery.md, BRIDGE-lean.md, provenance.json, checks/ + logs/, sources/, lean/.

## Honest limitations

- Theorems cover k ∈ {4,5} all n (plus symmetry columns n ∈ {3,4}); **not** the full conjecture (open: k ≥ 6 ∧ n ≥ 5).
- Lean bridge is scaffolding with `sorry` — explicitly not a proof; not submitted for formalization credit.
- Prop 2.3's all-Q exactness is proved by a mechanical derivation sketch (classical denumerant quasi-poly structure) + verified vs series Q ≤ 9; a fully self-contained write-up of that derivation is future work.
- Credit claimed: 0 (per task rules; awaiting review).
