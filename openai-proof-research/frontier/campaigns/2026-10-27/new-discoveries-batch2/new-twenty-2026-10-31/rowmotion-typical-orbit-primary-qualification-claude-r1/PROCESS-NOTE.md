# PROCESS-NOTE.md — late disclosure, supplementing REVIEW.md

After writing source-map.json and review.json, I ran one direct `python3 -I -B -c` JSON validity check on those two own products outside run.py, under an outer timeout of 60 s. It read only those two files, wrote nothing, printed "json ok", and touched no frozen, helper, protected or network resource. It was a deviation from "all other substantive local work goes under run.py". It is disclosed here and not repeated.

The review-file statements "lane receipts record the runner's true exit" for denials chunks 07-10 and "no redirects" for the GET hops are checked by the seal run from the receipts and the guard ledger.
