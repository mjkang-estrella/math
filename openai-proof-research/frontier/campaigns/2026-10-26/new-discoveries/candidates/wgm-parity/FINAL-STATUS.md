# Final proof packet status

The independent source, mathematics, formal, bounded novelty/eligibility, and
manuscript review passed. The full report and its original provenance are in
reviews/. All 34 original reviewed files are preserved byte for byte;
frozen-parent-hashes.json binds that checkpoint. In particular, credit0 and
pending-review phrases in README.md, candidate.json, provenance.json and the
unchanged reviewed paper describe the earlier review freeze.

Campaign acceptance is recorded separately in ledger.json only after the
parent assembles this deterministic archive and performs a fresh strict replay
from the extracted raw sources. A local acceptance.json, when present beside
this archive's extracted files in candidates/wgm-parity, binds that later
acceptance to the ZIP hash; it is not part of the self-hashed archive.

The theorem resolves Wang2024 Section7 open question(2), for every positive
integer weight tuple with odd total, with no gcd assumption. It is ONE outcome.
The old MathDB349081 cardinality question was already proved by Wang and is
not credited. No optimality/equality classification is asserted.

Reproduce: run verification/verify_candidate.py with this directory as the
candidate, --lean-bin set to Lean4.34.1, and --packages set to the mathlib
package directory matching verification/pins.json. Only raw .lean sources
are bundled; no prebuilt object is trusted.
