Read SUMMARY.md. Development uses readonly r9/build then r7/build after own build, no copying old oleans. Final full replay must rebuild all sources with neither old path. First new module must contain and compile a real nontrivial family case, then retain receipts and advance incrementally.

## 2026-11-06 r10 progress (Pi GLM5.3Flash)
- frozen-before: 581/581 OK (receipt frozen-before.json).
- src/CrownVFamCutA.lean STRICT EXIT 0. sha256 42882e8c20b62128bde738ea056167caebee5bb0feb5d53a53fed5b9ce7eaafb. receipt 1793980863800786303_lean_CrownVFamCutA.json. olean build/CrownVFamCutA.olean.
- Contains: existsFinThird/existsFinApart (index availability, n>=3), not_sideX_inr/not_sideY_inl/vidx_inl_eq_inr, and Cutset for famCut of zero/fullX/fullY/delX i/delY i (any 3<=n; full sides need two survivors apart, delete-one uses the erased-index isolation).
- Method: witnesses Sum.inl/Sun.inr pairs with SameC.two through t; refutations via sameC_eq_of_forall_not_sEdge on the true edge relation (witness isolated in complement; delX/delY use vidx collision after complement-membership pinning).
- Remaining: mix i j (i!=j) cases, FamValid, combined all-valid-families theorem (wave 2, CrownVFamCutB), converse, full local-v=4, audit/replay.
