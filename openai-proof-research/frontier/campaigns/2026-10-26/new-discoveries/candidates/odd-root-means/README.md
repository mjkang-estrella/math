# Odd-degree derivative-root mean identity: MathDB 336466

This packet proves Conjecture 2 of Wojnar–Wojnar–Brin, arXiv:1706.08381v2, for every odd-degree complex polynomial. The alternating binomial sum of the means of the polynomial evaluated at its successive derivative roots is zero. Roots are counted with multiplicity; no real-rootedness, simplicity or genericity assumption is imposed.

The proof continues normalized Newton root moments polynomially in the remaining derivative degree. The artificial zero-parameter mean is a classical apolar self-pairing, which vanishes in odd degree. A finite difference gives the exact source identity. Classical Newton identities, finite differences and apolarity are credited; the full source-conjecture resolution is one outcome, not one credit per degree or lemma.

## Contents and replay

- `paper.pdf`, `main.tex`: complete four-page manuscript, including primary-source and novelty qualifications.
- `formal/`: six frozen modules, 50 declarations, complete arbitrary-polynomial source bridge.
- `reviews/independent-final-review.md`: independent mathematical, exact-source, formal and manuscript review.
- `reviews/nearest-prior-investigation.md`: detailed original primary-source comparison.
- `verification/`: exact dependency pins, independent isolated replay receipts, declaration types/axioms, visual QA and verifier.
- `sources/provenance.json`: primary URLs/hashes; third-party full articles are referenced rather than redistributed.

With Lean 4.34.1 and the exact compiled dependencies in `verification/pins.json`, run from the packet root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The verifier checks exact dependency revisions and tracked-file cleanliness, compiles isolated byte-identical copies with warnings as errors, and checks all inventoried types and axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. There are no proof holes, extra axioms, `unsafe`, or `native_decide`.

The endpoint `OddRootMeans.source_conjecture_336466` assumes only `p : ℂ[X]` and odd natural degree. It uses actual derivative-root multisets and the exact source denominator; no missing root/moment/source bridge is supplied as a hypothesis.

## Material novelty limitation

Independent review recommends one source-conjecture resolution under the documented-prior-art/no-known-prior-resolution standard. The closely related Toda 1936 and Popoviciu 1940 formulas were read, including rendered originals; they do not explicitly state the same-degree self-test and apolar boundary needed here. Toda's 1934 precursor could not be read in full because its publisher returned an anti-bot page. This material limitation remains explicit. The later descriptions do not rule out every possible additional formula in that unread paper. No absolute worldwide priority is certified.

No classification of all mean relations or other source conjecture is claimed. No external publication, author contact, posting, upload or push occurred.
