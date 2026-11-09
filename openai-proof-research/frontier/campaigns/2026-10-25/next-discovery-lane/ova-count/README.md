# MathDB 350342: ready for parent review

**Full outcome:** There exist prime inputs p=677 and q=401 for which the source construction yields at least 38 distinct prime outputs, disproving both N≤10 and N≤13.

**Status:** the complete Lean module passes the pinned verifier. Independent parent review is pending, so this lane has not counted or released it as accepted.

## Source

MathDB 350342 states N≤10 and points to arXiv:2104.04522. The retrieved arXiv v1/v2 use the construction while citing Theorem 7 of the 2020 Revista Politécnica paper, DOI 10.33571/rpolitec.v16n32a10. That original paper’s Conjecture 1 (printed p.117) states N≤13. The source mismatch is explicitly recorded, and the same witness refutes both.

The exact fetched post, including all posted solutions, is in `source.json`; raw response and original papers are archived in `../sources/`. `primary-reference.json` records hashes and the credited reply.

## Proof

The input residues are 317 and 41, and both frequencies equal 1. Thus the two primality conditions become Prime(360-r) and Prime(720+r). Thirty-eight explicit residues satisfy the bounds and both primality conditions. Their output values 720+r are distinct. Each output prime itself witnesses that r is a prime residue class modulo 360. Finset inclusion and injectivity prove at least 38 distinct outputs.

## Deliverables

- `main.tex`: detailed manuscript; `build/main.pdf`: built paper.
- `formal/OvaCount.lean`: complete single-module proof.
- `formal/Checks.lean`: declaration and axiom checks, copied from the pinned verifier.
- `build/audit.json`: compiler receipt; `build/Checks.log`: full declaration/axiom output.
- `coverage.json`, `NOVELTY.md`, `self-review.md`: scope and review notes.

Run from the campaign directory:

```sh
python ../twenty-proof-campaign/verify_outcome.py ova-count
```

The verifier uses Lean 4.34.1 and the already installed package revisions in `pins.json`. The canonical main theorem is `OvaCount.prime_count_counterexample`. Its module has 20 audited declarations. No omitted proof placeholders or non-kernel computation are present.

## Limits

The theorem proves a lower bound of 38, which fully refutes the conjecture. It does not assert that 38 is the exhaustive total, despite that claim in the prior post. It does not use or verify the source’s general existence theorem, nor any Goldbach claim.

The input pair and all 38 residues are from Shivam Patel’s MathDB response dated 2026-08-20 (UUID cb893380-2a3c-48d8-92d6-21c99c7f1ce8). This is a formal verification of that known posted counterexample, not a new discovery. A targeted exact-phrase search did not add a different earlier source, but this is not proof of literature priority.
