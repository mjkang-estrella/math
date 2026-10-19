# r116 research packet

Start with research-report.md, then frozen-target.md and proof.md. operation-comparison.md and reading-ledger.md are essential qualifications, including the direct I52 antecedent and late reads. screens.md records the unequal unselected screens. There is no independent correctness, contribution, count or acceptance assignment.

public/ contains original research prose, factual source metadata and verification code. private/ contains necessary reading evidence under its original rights. See RIGHTS.md before redistribution. This is not a publication package.

The read-only integrity verifier requires TWO detached anchors supplied independently of the packet: the SHA256 of manifest.json and the SHA256 of the external FINAL.json. From this directory's parent run:

    python -B packet/public/verify.py --packet packet --finalhash MANIFEST_SHA256 --finalfile FINAL.json --finalanchor FINAL_SHA256

Do not substitute a digest computed from the potentially untrusted input as an independent anchor. The handoff and outside-packet integrity-controls.json record the actual hashes. FINAL.json binds the report, proof, frozen target and verifier. Exact file/directory membership, modes, lengths, SHA256, regular-file and no-hardlink/symlink conditions are checked. The verifier writes nothing. Copy-based controls separately test failures and preservation of originals.

Integrity establishes byte identity only. It does not prove the universal mathematics or decide its contribution. No finite mathematical experiment is used as a replacement for the general proof.
