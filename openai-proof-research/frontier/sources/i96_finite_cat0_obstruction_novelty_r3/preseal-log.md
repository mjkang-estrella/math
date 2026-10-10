# I96 preseal record

Only I96-owned paths were changed. Original I89/I91 bytes were never repaired or resealed.

1. The first I96 symbolic-elimination run rejected a Young-row argument/sign ordering at an assertion checking the isolated variable coefficient. The row invocation was corrected to c,P;A,w with q=2/5 and negative sign, and c,w;C,Q with q=5/2 and positive sign. The corrected independent computation cancels all variables with nonnegative exact rational multipliers. No failed trace was used as evidence and no original I91 row was changed.
2. The first reference-capture run assumed both historical seals stored file lists. I89 stores a mapping while I91 stores a list; the capture script was corrected to handle the two existing formats without changing them.
3. The first selected-PDF inventory used the kind name `pdf`; I79's actual kind is `outside_pdf`. It produced zero selected PDF records. The capture was corrected before validation; the final inventory contains eight selected PDFs. No claim of PDF re-extraction relies on the zero-record draft.
4. A diagnostic read requested `snapshots/inputs.json`; the actual frozen input manifest is `inputs.json` beside `snapshots/`. The failed read did not change any file. Final verification uses the actual manifest and checks all five snapshot hashes.

Historical capture tools (`capture.py`, `bind.py`) may write owned evidence and are not verifier commands. Verification invokes only the offline verifier, unchanged historical verifiers, exact checks, `rg`, and `pdftotext` with stdout output. The final seal will be created once, only after the final candidate passes preseal validation. No seal is created by a verifier.
