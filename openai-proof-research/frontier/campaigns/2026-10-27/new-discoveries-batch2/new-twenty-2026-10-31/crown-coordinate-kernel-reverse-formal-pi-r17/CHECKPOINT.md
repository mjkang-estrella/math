# r17 CHECKPOINT

State: both new modules sealed, compiled strict, axiom-audited, leanchecker-clean.

- src/CrownVCoordDiff.lean  — CrownV.coordKill_sub_mem_span (arbitrary-p difference lemma); exit 0; receipt 1794003662473566654; sha f47eb2ad7f71b07c06003be69eae1289e340176d3049bedbf83ef8717eb1b69d
- src/CrownVCoordKernelEq.lean — CrownV.coordKer_le_span + CrownV.coordKill_ker_eq (ker = span coordGens T); exit 0; receipt 1794004034431699188; sha 80c09644750d67c3eba2b958bf5e3bcd790055767e4f3aedf985e03a9d726af7
- audit/CrownVCoordKernelEqAxioms.lean — axioms [propext, Classical.choice, Quot.sound] x3; receipt 1794004164230271441
- leanchecker CrownVCoordKernelEq exit 0; receipt 1794004165328709076; post-checker hash verification true
- verify_frozen before/after: 866/866, 0 mismatches each
- Bootstrap receipt preserved: bootstrap-receipt.json (untouched)

Next (unpaid): fullside primality; noncoordinate families; J-structure/direct
colon; homogeneous degree 0..3 all fields incl char2; quartic exact colons/VIs 4;
negative controls; fresh extracted replay; independent review; paper; acceptance.
Credit 0; 52/60 unchanged.
