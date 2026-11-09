# Proof and scope

DRAFT; root alone decides acceptance. No priority claim.

For M_(2n), vertices are integers from 0 through 2n−1; cycle edges precede antipodal chords. For n=6 the label list is

17 13 7 8 3 15 6 18 4 5 12 2 | 10 1 9 16 14 11.

It is a permutation of 1,…,18. The induced sums are

29 31 29 31 25 29 31 25 31 25 31 25.

Every consecutive pair (including wraparound) differs. Antipodal pairs are (29,31), (31,25), (29,31), (31,25), (25,31), (29,25). Therefore this is a three-colour local antimagic labelling. The odd cycle 0,1,2,3,4,5,6,0 proves the lower bound three, so χ_la(M_12)=3. Substitution n=6 refutes the even-n≥4 universal conjecture.

For M_8 the label list 11 2 9 12 5 10 6 8 | 3 7 4 1 induces sums 22 20 15 22 20 22 20 15. Its cycle and chords are proper, and 0,1,2,3,4,0 supplies the lower bound. This disproves the order-eight theorem, independently of the M_12 example. The source's 132 total must be 156.

The fresh arithmetic checker, scripts/verify.py, independently reconstructs edges and checks all these assertions. verification.json records the incidence additions, distinct colours, colour-class sizes and total sums. It also records two deterministic finite label-swap searches; their failure is not a lower bound or a classification.

The exact formal endpoint is

```lean
Mobius.conjecture_false : ¬ (∀ n : Nat, 4 ≤ n → n % 2 = 0 →
  Mobius.LocalAntimagicChromaticNumberEq n 4)
```

The family-specific attained-minimum relation has both an attainment and a universal lower-bound clause. The witness with three colours contradicts the lower-bound clause at four. The packet does not formalize the lower bound three or the M_8 remark. Its M_12 graph-encoding bridge includes simple edges, valid endpoints, no loops and literal adjacency. See the unchanged sources in packet-safe-extract/ and Section 4 of the draft.

No Lean execution occurred in this lane. The root's prior replay receipt reports successful compilation and explicit kernel-checker runs for both packet modules, and endpoint axioms limited to propext, Classical.choice and Quot.sound. Packet hash ffa01d95d108d91cc5f90638a1ef46fd9f76ac2cc743487a2c0b9644e2f7a2ea. The local safe-extraction test checks the exact three allowed member names and rejects traversal, absolute names and symbolic links; all extracted bytes are hashed.

STEP 0 was completed before paper.md was authored. It found no stop-trigger in the bounded scope documented by prior-art-completion.json. Missing workshop mathematical slides, the incomplete journal body/correction history and bounded construction-comparison scope remain explicit limitations. There is no claim of exhaustive novelty clearance.
