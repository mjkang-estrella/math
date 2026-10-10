# Pre-seal development record

1. Initial all-domain search completed (235 output lines); family-name postprocessing then raised IndexError because two bibliography continuation lines in PDF-derived text contained a form-feed that Python splitlines treated as a line break. Search bytes were retained. The corrected extraction only considers records containing `preprints/`; verifier separately replays the exact rg multiset including those continuation lines. No mathematical claim changed.

2. Expanded history capture adds first-phase reviews and uses snapshot paths for mutable ledgers; original output remains untouched.
3. A malformed duplicated revision in the draft odd-primes hyperlink was corrected before sealing. Mathematical statements unchanged.
4. First exact diagnostics run passed unchanged. The numerical rate around 0.065 is recorded only as a finite observation, not an asymptotic obstruction.

5. An in-memory unsealed preflight reproduced all 10,373 pinned blobs, 1,033 original outside bodies, 235 complete-domain search records, 194 immutable references, 25 passages, seven primary responses, three PDF text replays and all exact diagnostics. All four permitted mutable ledgers had drifted; snapshot replay passed and drift was informational. The final sealed run is separate.
6. Verifier supports an optional externally supplied seal SHA-256; its own ordinary mode prints the digest. No source fetching or resealing is part of either mode.
