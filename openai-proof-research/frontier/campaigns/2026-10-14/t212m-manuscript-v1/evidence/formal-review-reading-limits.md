# Reading limits

Read in full: `T212M.lean`, `Controls.lean`, `README.md`, `coverage.md`,
`provenance.md`, `rebuild.py`, `verify.py`, `integrity_controls.py`,
`validation/Checks.lean`, `inputs/binding.json`, `manifest.json`, `lakefile.toml`,
`lean-toolchain`, and the fresh and frozen `types-axioms.log`.
`lake-manifest.json` was checked by machine (nine pins), not read line by line.

Author candidate (r74, authenticated): `candidate-proof.md` lines 1–260 in full
(claim, §§1–5), the rest located by search only; `label-stability-interface.md`
lines 95–139 (the use-site, lines 110–133); `tail-and-modification.md` lines 1–59
to confirm it is a different (infinite-change, circuit-replacement) argument;
`dh-limiting-coupling.md` by keyword search only. No other r74 file, and none of
the upstream manuscripts, was read. I did not assess the truth of the r74
probabilistic claims; only the match between the formal statement and the
deterministic finite-change lemma.

Not read or used: parallel T212M proof, contribution and manuscript reviews,
parent intake/adoption files (`../t212m-parent/` was only listed by a hash search),
shared ledgers. The prior `../t205m-formal-review-r1/` helper was read and adapted
(provenance in `run_review.py` header); its verdict was not used.

Trust: cached dependency `.olean` files and the Lean binary are trusted. No
independent kernel replay (lean4checker) was run. Byte identity of fresh records
with frozen ones shows reproducibility, not independence of the toolchain.
