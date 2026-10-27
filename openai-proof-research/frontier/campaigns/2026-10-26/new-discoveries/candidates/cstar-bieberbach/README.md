# Globally injective C*-power series violating Bieberbach order bounds

Read paper.pdf, PROOF.md, the formal source endpoint, reviews/final/review.md and reviews/parent-final-addendum.md.

Reproduce with pinned Lean4.34.1 and the packages in verification/pins.json:

    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages

Expected: 28 declarations in 4 modules, all module logs empty, only propext/Classical.choice/Quot.sound. Parent and fresh independent receipts agree. The immutable archive still requires a fresh extracted replay.

All 25 reviewed originals are preserved. Only the release TeX/PDF/QA are updated for final-review status; proof/verifier bytes are unchanged. The later acceptance.json outside the archive governs any discovery count. Historical credit0/pending snapshots do not assert present acceptance.

ONE source-question outcome combines the general-coefficient
Conjectures1.2/1.4. The fixed parameter8t is formalized; no parameter-family
or invertible-coefficient/polynomial/Robertson/Lebedev-Milin side credit.

Parent clarification of two ancillary reviewer phrases: CStarRing is a norm/star
class and does not itself impose an order. The claim uses the actual pointwise
ComplexOrder on C([0,1],C), with its genuine StarOrderedRing compatibility;
this is the source positive-cone order. The explicit elementwise calculation
at t=1 proves the violation. Also the witness has scalar-fiber zeros, not a
second global zero element (it is globally injective with F(0)=0). For example
u(t)=pi*i/4 has norm<1 and F(u)(1)=0 while u(1)!=0, so an invertible exponential
multiplier factorization cannot hold. Neither ancillary wording is relied on
by the Lean endpoint or the manuscript.

Actual author-deposited Zenodo6917925 bytes are used; directPreprints403 remains
a disclosed limit. Whole-text agreement and fresh live deposit checksum were
verified, but binary identity of the deposits is not claimed.
