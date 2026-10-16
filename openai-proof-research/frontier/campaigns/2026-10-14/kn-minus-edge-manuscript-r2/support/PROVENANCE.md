# Provenance of the code in this package

All checks are finite. They test identities, bookkeeping and hypotheses used in the proof. None is part of the proof, and none establishes Theorem A for all n.

## New code (written for this package, MIT)

| File | Purpose | Arithmetic |
|---|---|---|
| `release_checks.py` | Checks R1–R9 (Table 2 of the paper). R1 closed forms, n ≤ 3000. R2 two-page deletion count, 4 ≤ n ≤ 56. R3 even identity, 6 ≤ n ≤ 3000. R4 OWH Thm. 3.1 routine range and the gap identities of Sec. 7, odd n ≤ 401. R5 Corollary B algebra, 4 ≤ m ≤ 400, 1 ≤ n ≤ 12. R6 rectangular and twisted detector ranks, s ≤ 5, every twist node. R7 dimensions of S_a, S_b and S_a ∩ S_b, s ≤ 6. R8 degree budgets and the missing-pair identities (3.2) for the tests of Lemmas 3.4 and 3.6, 3 ≤ s ≤ 7, with enforced controls that each twist factor is needed and that the untwisted upstream test is inadmissible. R9 four-orientation factor and the non-converse H = xy for random skew forms (not drawings), n = 7, 9. Fixed seed 20261016. | Python integers with `//` only and `fractions.Fraction`; no floating point in mathematical arithmetic (runtime uses `time.monotonic`). Every check goes through one `check()` function that records failures and makes the script exit 1; `python -O` cannot disable it. |
| `run_all.py` | Fail-closed runner (see README). Exit 1 on any nonzero exit, any output line containing `FAIL`, a missing success line, a stdout mismatch with the frozen output, nonempty stderr, an inherited-copy hash mismatch, or `-O`. A self-test confirms that `SOME FAIL` with exit 0 is rejected. Inherited scripts run in fresh `checks/work-*` directories that are deleted afterwards. | — |
| `build.py` | Builds `main.tex` with Tectonic in a scratch directory, saves the log and receipt, renders all pages. Fails on overfull boxes, undefined references or rerun warnings. | — |
| `freeze.py`, `verify_package.py` | Write and recheck the public allowlist manifest, the deterministic ZIP, the output manifest and `SHA256SUMS`; `--with-inputs` rechecks `input-manifest.json`. | — |

Finding (5) of the prior reviews: the contribution reviewer's `gap-check.py` used a floating-point floor on small exactly representable integers. That script is not copied or run here. The same quantities are recomputed in R4 with integer and rational arithmetic only.

## Unchanged inherited copies (`inherited/`, MIT, author Myeongjin Kang)

The runner authenticates each copy against the SHA-256 recorded in the earlier manifests before running it. No byte was changed.

| Copy | Original | SHA-256 | Bytes |
|---|---|---|---|
| `author/kn_minus_e_checks.py` | `fresh-substantial-discovery-r2/checks/kn_minus_e_checks.py` | `1ee907a1779184faa3fe1b3c229d83d7332bedeb956f900ca8164901633f3364` | 16464 |
| `author/kn_minus_e_checks.out` | same directory | `bc5cbf6900104a6bc05cb0c9df99ddf5750281484a488c372aea0c1ceac5d3fe` | 3043 |
| `author/kn_minus_e_modp_large.py` | same directory | `18cfe155119d6d407cb7d26b5d9ec92660388165622df4bf1fae0d780ef94386` | 4286 |
| `author/kn_minus_e_modp_large.out` | same directory | `35f2508e427869ad5a4f9825e63869d03c6ef0377e437eba21e31f23165df20f` | 1204 |
| `reviewer/adversarial.py` | `kn-minus-edge-proof-r1/checks/adversarial.py` | `49d327f68c2841933bf2bc9f208e080af474b6c83c0e8ceca9a64985543ebcf1` | 12758 |
| `reviewer/adversarial.out` | same directory | `b27e836235ce25233fad65e00cd08a703a7dd6c2bbadd1c4a235c643647994ab` | 1141 |
| `reviewer/adversarial.json` | same directory | `45f868c8e6381e9c2cfa3b597be6f9b0fd6ffbd71755c8ac00eb758fb4a30691` | 1905 |

Arithmetic and known limits of these scripts, stated also in Sec. 8 of the paper:

- **Author stdlib checker.** Exact rationals for polynomial identities; floating-point coordinates and angles for the random straight-line drawings; ranks modulo 2^61 − 1; n ≤ 12. It prints the values of tests that violate the missing-pair identities but asserts nothing about them, so those prints are not negative controls. The enforced negative controls are R8 and R9.
- **Author mod-p checker.** NumPy arithmetic modulo 2^31 − 1; frozen log covers 13 ≤ n ≤ 19. On failure it prints `SOME FAIL` and still exits 0. The runner treats that output as a failure. For the original r1 package orders 15, 17, 19 were re-executed (`checks/run-receipt-large.json`, NumPy 2.5.4, interpreter in a local scratch virtual environment); every result line matched the frozen log.
- **Reviewer checker.** Independent controls by the proof reviewer, including n = 15; exact integer geometry, rationals, ranks modulo 1000003. The reviewer's earlier runs failed because the harness wrongly required some invalid tests to be nonzero (for example, at n = 15 the first chosen missing edge had no crossings in the full straight-line drawing). Those were harness errors, not counterexamples (`kn-minus-edge-proof-r1/review.md`, Section 12). The failed-run logs stay in `kn-minus-edge-proof-r1/checks/adversarial-*-control.out` and `adversarial-initial.out`, hashed in `input-manifest.json`, and are not copied here.

## Recorded runs

- `checks/run-receipt.json`: full runner, PASS (release checks 71.7 s; author checker 122.8 s, stdout identical to frozen without the timing footer; reviewer checker 25.4 s, stdout byte-identical, JSON identical except runtime). Python 3.14.7, Linux x86_64.
- `checks/run-receipt-large.json`: mod-p subset n = 15, 17, 19, PASS, 1196.5 s.

## Revision r2

Mathematical checker sources and run receipts above are unchanged r1 evidence. Only the packaging verifier is revised: `--public` validates a clean extraction, rejects missing/corrupt/unlisted files, duplicate or unsafe paths and symlinks, and optionally authenticates its manifest against an external hash. Full-directory checks remain available. Build and visual receipts are regenerated for r2. No new Lean compilation or long modular run is claimed.
