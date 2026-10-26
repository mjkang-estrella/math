# Nonconvergence for all finite all-odd randomized subtraction games

One proposed new resolution of the all-odd nonconvergence assertion explicitly left open in Capitelli–Somma, arXiv:2405.19593v1, Section 3. The actual recursively defined winning probabilities have no real limit for any nonempty finite set of positive odd moves. The proof also certifies a conserved quantity bounded below by the number of allowed moves.

This is a question in the primary source associated with MathDB 363319. That MathDB record itself asks a different question, simplicity of all characteristic roots. **The root-simplicity conjecture remains open.** This packet bypasses it and does not claim to resolve that record.

The new result covers arbitrary cardinality, not just the already known singleton and two-move cases. All lemmas, boundary cases and the positive-invariant conclusion belong to this one combined discovery outcome.

## Contents and reproduction

- `paper.pdf` and `main.tex`: complete three-page paper.
- `formal/`: six Lean modules, 37 explicitly inventoried declarations including the model structure.
- `reviews/independent-review.md`: exact-source, mathematical, novelty and final formal review.
- `verification/audit.json` and `independent-audit.json`: independent isolated pinned replays.
- `verification/declaration-types-and-axioms.log`: all inventoried types and axiom dependencies.
- `sources/provenance.json`: primary-source URLs and hashes; article PDFs are referenced rather than redistributed.

With Lean 4.34.1 and the exact compiled dependency revisions in `verification/pins.json`, run from the packet root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The verifier checks exact dependency revisions and tracked-file cleanliness, compiles byte-identical isolated source copies with warnings as errors, and checks each inventoried declaration's type and axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; no proof holes, extra axioms, `unsafe`, or `native_decide` occur.

The main endpoint is `OddSubtraction.all_odd_game_nonconvergence`. Its only hypotheses are that the finite move set is nonempty and all moves are odd; positivity follows from oddness. There is no unproved probability-model, invariant, spectral, or gcd assumption. `OddSubtraction.all_odd_game_positive_invariant` supplies the quantitative bound.

No external publication, author message, posting, upload or push is implied by this local packet.
