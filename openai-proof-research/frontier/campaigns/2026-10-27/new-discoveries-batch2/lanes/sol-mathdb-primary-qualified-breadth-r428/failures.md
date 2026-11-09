# Failures and access limits

Two initial guarded preflights failed before scientific assessment. First: TypeError, list indices must be integers or slices, not str, because r304 manifest is a list rather than an object with files. Second: AssertionError on r304/README.md because the manifest omits size and the first checker required size==None. The corrected checker validates its declared SHA256 and records actual byte size. These were parser/schema failures, not altered sources. Both runs exited1 under the fixed guard (peak group RSS under37MB); the successful preflight exited0. No upstream verifier was executed and no upstream receipt was written.

Successor attempt https://pure.mpg.de/pubman/item/item_3121336_2/component/file_3121337/Rowlett_fundamental%2Bgap_oa_2013.pdf returned HTTP403 on 2026-10-31. Stopped; no retry, alternate host, or route sought. See successor-provenance.json. The triangle-gap item remains HOLD_SUCCESSOR_ACCESS despite a precise public theorem search lead.

Inherited AIM/Kourovka/EGRES denials, AIProofWatch403, MathDB429 and the rigid-body successor403 routes were not retried. Zero MathDB requests. No browser, account, Google, GitHub API/raw/codeload/diff, ScienceDirect access, TLS bypass, messages, uploads or publication. Public search produced unsolicited links to barred/irrelevant destinations; none was opened.

No current public-proof registry head is available in this packet. r304/r363 are verified historical/local exclusion evidence only. Every unresolved item retains HOLD; no missing source or registry was treated as evidence of hardness or novelty. Published-theorem retirements require no claim of current absence of proofs.

Only the cited report pages and explicitly retained adjacent excerpts and successor sections were inspected. Entire downloaded reports are not claimed as read. No complete version-history comparison or dependency closure was performed. No expensive sweep, new formal proof, or manuscript was attempted.
