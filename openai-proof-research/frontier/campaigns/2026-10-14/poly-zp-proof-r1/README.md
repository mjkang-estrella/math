# poly-Z_p proof review, round 1

The verdict is in [review.md](review.md). The mathematics passes, with two
required wording corrections (R1, about sharpness of the c_t congruence at
p = 2, and R2, about the Theorem B dependency list) and one required
literature addition (R3, Frankel 2016, Chapter 4). No counterexample or gap
was found. Contribution is not assessed here.

Verify (read-only, offline, Python 3.10+ standard library):

```sh
sha256sum seal.json   # compare with the handoff value
python3 -B verify.py
```

Layout: `checks/adversarial.py` and its frozen receipt `checks/adversarial.json`;
`receipts/` (candidate verifier PASS output and tamper-test stderr);
`private/` (third-party reading copies, not releasable); `commands.md`,
`provenance.md`, `retrieval-literature.json`, `RIGHTS.md`, `LICENSE-MIT`.
Prose CC BY 4.0, code MIT, author Myeongjin Kang (no affiliation).
