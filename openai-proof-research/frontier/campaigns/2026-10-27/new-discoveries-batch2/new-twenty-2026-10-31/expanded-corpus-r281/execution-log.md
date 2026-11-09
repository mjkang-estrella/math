# Execution log

Research tools only; no mathematical solver or numerical experiment. Child count0.

extract.py: Python-I-B, timeout140s; CPU120s, address-space6GiB. Completed,20records extracted. First reservation SHA printed before extraction and asserted again by script.
fetch.py: Python-I-B, timeout140s; CPU120s/address-space6GiB, two concurrent HTTP workers,12srequest timeouts,16MBresponse cap. Completed. receipts.json.
bodies.py: same runtime/resource bounds, two HTTP workers, sequential pdftotext subprocesses with20stimeout. Completed. body-receipts.json. All assigned arXiv history versions requested explicitly.
passages.py: Python-I-B; completed in tool cell. Text extraction only, no mathematical execution. Target-passage file deliberately exceeds actual read depth.
extra.py and hegarty.py: Python-I-B, timeout140s; inherited CPU120s/address-space6GiB, <=2HTTPworkers. Completed. Extra receipts and published Hegarty proof inspected.
finalize.py: Python-I-B, timeout140s, CPU120s/address-space6GiB. Completed exact-key assertion, allrawhashchecks and all10chunkrechecks.

Initial filesystem listing/search output was truncated and is not a coverage claim. A broad historical prose/source rg subprocess was interrupted via Ctrl-C after no delivered output; exit130 observed. It did not produce evidence or novelty clearance. A replacement focused search had a60sCPUlimit,6GiBaddress-space limit,60ssubprocess timeout and2MBfile-sizefilter; it completed. Initial read-only commands and passage-printing snippets did not each carry explicit per-process resource caps; no stronger blanket resource-compliance assertion is made. None performed substantial computation. These limitations are disclosed rather than retroactively inventing run receipts.

All writes are under this lane. No external cache configured by the scripts; pdftotext creates the specified lane-local text files. Script warnings about Python regex escape notation are cosmetic and did not fail extraction. One optional bs4 HTML parsing attempt failed because the module was absent; subsequent plain-text reading used the standard library; no package installed.

End-of-task process inventory checked for lane scripts and matching rg/pdftotext jobs; only the inventory command itself appeared. No live job left.
