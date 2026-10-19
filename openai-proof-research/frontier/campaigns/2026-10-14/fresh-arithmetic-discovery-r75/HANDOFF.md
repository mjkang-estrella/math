# Arithmetic r75 handoff — detached seal

Status: no frozen target; no nominee; no count/gate assignment. Parent integration only. The campaign was supplied as 18/20; this packet requests no change.

Read packet/public/research.md together with packet/public/reading-limits.md. Six main operation-level screens covered integral Donovan finiteness, ramified Gersten kernels, intersection multiplicities, relative resolutions, nonsingular group equations and integral surface motives. Additional historical gluing/tautological screens did not yield a fresh mechanism. The newer Huryn–Newman effective-motive kernel distinction is attributed to that primary work; it is not a nomination or a truth audit of stipulated upstream.

Detached FINALHASH (SHA256 of exact packet/manifest.json):

    415cc5ab3688cd81263aa590993dd37c9ddb4d939b39c9b2fea0f231fca72665

Detached SHA256 of research.md:

    2cf1e9aaff1c3a339908fb70c360da0628af37e7000b5c5db23aa136dfb43d78

Detached SHA256 of integrity-controls.json:

    448932cede2f9bb9469f9294e4f05cdf9aebbd690e583538ddc6906d4856e9cd

Run from this directory:

    python -B packet/public/verify.py --packet packet --finalhash 415cc5ab3688cd81263aa590993dd37c9ddb4d939b39c9b2fea0f231fca72665

The final copied baseline and eleven rejection controls behaved as expected. They test integrity only. The first run correctly rejected an unsorted initial manifest, preventing a false baseline success. That original report is retained as integrity-controls-first-run.json. The manifest entries were sorted by their serialized relative paths, a new detached hash was computed, and all controls were rerun. No mathematical text or scope was changed in this repair. Each copied-control run checked that its original packet was unchanged; temporary copies were removed.

The seal contains 66 payload files plus the manifest, including 41 authenticated pinned source bodies and six primary PDF/text pairs. Receipt retention does not imply complete semantic reading: the limits are explicit. private/ retains source bodies under original rights; public/ contains original prose and the read-only verifier. No formal/manuscript/release work, uploads, browser UI, shared-index edits, git staging/commits, contacts or nested agents were performed.
