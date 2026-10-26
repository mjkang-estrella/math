# Exact counterexample to Kovalev's trigonometric positivity conjecture

MathDB 369172 / Kovalev, *Sharp bounds for some segments of bounded power series*, Conjecture 1.3 (2025 preprint; 2026 published version).

For the normalized Taylor coefficients of sqrt(1+z+…+z^49), the cosine partial sum through degree 949 is strictly negative at t=arccos(523/527), approximately −0.000475321859370024. This is one counterexample outcome. It does not refute the separate zero-free Conjecture 1.2 / MathDB 369171, and no minimality claim is made.

## Proof and certificate

The seven Lean modules construct the actual normalized formal square root, derive its exact coefficient recurrence, identify all 950 coefficients with finite integer data, prove the rational-cosine Chebyshev identity, and transfer the kernel-checked negative integer Horner result to the real trigonometric sum. The main endpoint `KovalevCounterexample.explicit_source_counterexample` has no hypotheses; `conjecture_369172_false` negates the complete universal statement.

- `paper.pdf`, `main.tex`: complete three-page paper.
- `formal/`: 55 inventoried definitions, lemmas and theorems; complete seven-module certificate.
- `certificate/integer-sign.json`, `exact-numerator.txt`: full signed 3152-digit Horner numerator and denominator 2108^949, with exact rational data.
- `scripts/regenerate_certificate.py`: standard-library rational generator for the literal finite data and its balanced lookup representation.
- `reviews/`: independent exact-source, mathematical, numerical, final formal and manuscript review.
- `verification/`: pinned verifier, complete types/axioms, independent receipts, and visual paper QA.
- `sources/provenance.json`: actual primary-source locations and hashes; third-party articles are not redistributed.

## Replay

With Lean 4.34.1 and the exact compiled dependencies in `verification/pins.json`, run from this packet's root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The isolated replay checks all inventoried declarations with warnings as errors, exact dependency commits and tracked-file cleanliness, and only `propext`, `Classical.choice`, and `Quot.sound`. The large integer checks use ordinary kernel-checked `decide`. No `native_decide`, proof hole, extra axiom or floating-point sign test is used. The numeric module uses balanced lookups to avoid repeatedly normalizing a large array.

Optionally regenerate the literal numeric certificate from exact rational arithmetic:

```sh
python3 scripts/regenerate_certificate.py
```

This writes `formal/TrigCertificate.lean` and a build metadata JSON in the current directory. Its expected source hash is `86cd4e317fcf9909f4fcef4a0295b396840bb7724033c69195e7bf5b6190b0a3`. Generation is not trusted by the proof: the defining recurrences and sign are checked again inside Lean.

The actual public 2026 publisher PDF retains the conjecture unchanged. No earlier counterexample was located in the documented primary-source investigation; absolute worldwide priority is not certified. No external posting, author contact, upload, publication or push occurred.
