# kn-minus-edge-proof-r1

Independent adversarial proof review of the frozen `fresh-substantial-discovery-r2` candidate.

**PASS** for the complete Theorem A and Corollary B under the user-stipulated pinned OpenAI mathematics. No required mathematical repair found. This is not campaign acceptance, a contribution/priority verdict, a manuscript review, or a full formal certificate.

- `review.md`: full step-by-step verdict, including external scope checks and limitations.
- `checks/authenticate.py` and `checks/authentication.json`: all 33 frozen manifest entries authenticated.
- `sources/kn-main.tex` and `sources/upstream-authentication.json`: freshly downloaded pinned source and matching SHA-256/Git blob identity.
- `checks/author-exact-rerun.out`: full successful reproduction of the author stdlib checker.
- `checks/adversarial.py`, `.out`, `.json`: independent exact and modular support, including the new odd range n=15.
- Early `checks/adversarial-*.out` logs: invalid-test controls that exposed overly strong expectations in the reviewer harness, discussed in `review.md`.
- `provenance.json`, `input-manifest.json`, `output-manifest.json`: read extent, rights and byte/hash records.

From this directory:

```sh
python3 -B checks/authenticate.py
python3 -B checks/adversarial.py
python3 -B ../fresh-substantial-discovery-r2/checks/kn_minus_e_checks.py
```

Python 3 standard library only; the independent checker ran in about 26 seconds on the review host. Computations support the proof audit; they do not prove the all-n conclusion. No author code is imported by the independent checker.

Author metadata for original review artifacts: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. The copied upstream manuscript remains OpenAI-authored source material under its original rights; it is not relicensed. The external primary publisher text was read from the authenticated frozen snapshot; a fresh live publisher request returned HTTP 403. No external text was newly republished by this review.
