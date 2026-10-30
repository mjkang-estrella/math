# Preserved root read failure

Initial bounded cat requested nonexistent worker verify.py and returned exit 1 while reading the two actual checkers successfully. File inventory identified seal.py as the actual verifier. Root inspected it and wrote an independent, nonmutating verifier; no worker receipt was overwritten.
