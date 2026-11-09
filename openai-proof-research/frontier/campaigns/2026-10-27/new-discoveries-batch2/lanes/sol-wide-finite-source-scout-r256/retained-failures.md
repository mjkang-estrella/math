# Retained failures

1. Antisymmetric bracket multiplication doubles the commutator and loses characteristic-two information. Exact counterexample and successful replacement are in PROOF.md.
2. Author papers directory HTTP403, recorded in retrieval.jsonl; no retry, proxy, TLS change or browser bypass.
3. First finalize.py execution failed at the retrieval-hash assertion. citers.py had used the same output filename for two distinct OpenAlex work records. The first response had13985 bytes, hash6f5dda75ff8a62da937411d1e2da1d5164b1439ce6a0143118b7c70dda6070cc; the second969-byte response overwrote that filename. The original first response was preserved verbatim in citers.log. recover.py recovers the original bytes with an exact SHA match into a uniquely named file, with recovery.json mapping that hash to its recovered path. retrieval.jsonl stays unchanged; sources/bindings.json adds the remapping and retains the original logged path. No network retry or metadata reconstruction was used. The failed assertion was useful and is not hidden. Scientific primary PDFs were unaffected.

Current-registry and older-classical-body limitations are unresolved, not passing checks. Neither an empty title search nor a sparse citer list establishes novelty.
