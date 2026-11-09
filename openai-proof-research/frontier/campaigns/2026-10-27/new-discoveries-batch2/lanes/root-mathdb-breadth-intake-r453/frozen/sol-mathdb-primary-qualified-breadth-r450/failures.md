# Failures and limitations

- freeze.log and freeze-failed-v1.py preserve the initial failed run: the reader assumed every manifest was a dictionary. r304 uses a list. Corrected in freeze.py; freeze2.log records success before any scientific/historical content was read.
- primary-sections-partial.json preserves an early extraction taken while PDF downloads were completing. Empty pages in that intermediate are not access failures. The final extraction was repeated after all downloads completed.
- One exploratory shell sed command used an invalid address and exited 1; it read /dev/null and modified no file. Correct extraction used source text directly afterward.
- No 403, 429 or challenge occurred on the newly attempted EMS/arXiv routes. Inherited MathDB 429, AIM/Kourovka/EGRES, AIProofWatch, rigid-body and triangle-gap routes remain parked; zero requests to them. No Google, GitHub, ScienceDirect, browser, TLS bypass, public mutations or external messaging.
- Bounded searches are not a comprehensive successor review for all fifty. Only two targets received additional close successor theorem-section checks; none received full proof-dependency review or current proof-registry clearance. Missing clearance is HOLD, never hardness or novelty evidence.
- No mathematical helper calculations, finite sweeps, Lean, manuscript work or proof attempt. Guarded helpers perform integrity, extraction and lawful public HTTP reads only.
