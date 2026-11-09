# Preserved root failure

The initial guarded schema inspection successfully froze all r476 artifacts, then tried json.loads on final-receipt.jsonl. It exited 1 with JSONDecodeError: Extra data, line 2 column 1 (char 400). The receipt contains one scientific-integrity JSON object and one helper-guard JSON object. Corrected verifier parses both lines and checks PASS plus guard_exit=0. No bytes or receipt were changed, no mathematical result was used from the failed inspection. Root tool transcript retains the failed run; no source access failed.
