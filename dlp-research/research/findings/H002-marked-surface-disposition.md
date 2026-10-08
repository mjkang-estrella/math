# H002 V1: conditional reformulation, no extraction algorithm

Claude Opus `ecdloop-h002-marked-surface-review-20261008-r1` completed read-only
review. Raw retained separately. No experiment, Lean work or ECDLP gain. Root
accepts the elementary integer-matrix bridge, not all of the reviewer's verdict.

For Q=dG and M=[[a,b],[c,e]], preservation of ⟨(G,Q)⟩ is exactly
`b*d²+(a−e)*d−c=0 mod q`. The integer coefficient lattice in (a−e,b,c) has indexq
because the coefficient of c is−1. A pigeonhole box gives a short nonzero
relation O(q^(1/3)); with coefficients<q it is nonzero moduloq and yields at
most two roots. Given that informative triple, solve the quadratic and verify.
Given d, triple(1,0,d) works. This is a polynomial-time equivalence, not a
construction of the short triple. Testing each triple separately in a cube
of sideq^(1/3) enumerates aboutq triples; short-vector existence gives no gain.

For the prime-full-order case q=#E(F_p), pi−1 has kernel E(F_p); the matrix
[[pi−1,0],[-d,1]] has graph kernel and identifies the unpolarized quotient with
E². This strengthens the loss-of-information warning for abstract invariants.
It does not make the unknown marked isomorphism cheaply available.

Noninteger endomorphisms add a degeneracy: pi−1 acts as zero on rational points.
A matrix non-scalar in an abstract endomorphism ring may induce a scalar on
the q-subgroup. Require its reduced quadratic to be informative. Do NOT require
rewriting the entire integer-matrix proposal over the full ring: integer matrices
are a valid restricted search family. Recovering eigenvalues from arbitrary
explicit endomorphism representations is also a cost, not automatically free.

## Reviewer corrections and scope

- Equivalence to DLP does NOT show a reformulation has no algorithmic usefulness.
  Reductions often expose exploitable structure. The specific present gap is that
  no explicit sub-square-root extraction procedure has been supplied.
- A kernel-generator representation (G,Q) is already public and compact; saying
  every marked quotient description 'already contains d' confuses an encoded
  hard problem with an efficiently readable answer. A matrix with known integer
  coefficients and informative quadratic does permit efficient recovery; an
  arbitrary quotient representation requires its own conversion analysis.
- Every cyclic subgroup of q-torsion is isotropic for an alternating pairing.
  The review's 'cyclic non-isotropic' description is wrong. The relevant mismatch
  is induced polarization type(1,q) versus algorithms requiring principal
  polarizations and suitable explicit maps, not non-isotropy of the cyclic kernel.
- Integer scalar maps of magnitudeq^(1/3) can be evaluated by double-and-add in
  polylogarithmic group work. Dense degreeq^(2/3) is only a warning about dense
  symbolic output, not a universal evaluation lower bound. The original card's
  compact representation requirement remains appropriate.
- Square-root Vélu DOES concern a cyclic prime-order elliptic kernel; the raw
  phrase 'no cyclic-kernel version' is false if read literally. It does not give
  the needed abelian-surface extraction algorithm. A missing known formula is
  not a proved lower bound on all such constructions.
- The polarized moduli uniqueness claim is explicitly unproved; 'behaves like
  d↦dG', every possible kernel choice, cofactor extensions and LLL behavior are
  not accepted theorems. No tiny LLL experiment is needed for the current gate.

Primary sources inspected by reviewer: [Anni et al.](https://arxiv.org/abs/2503.08925)
and [square-root Vélu](https://arxiv.org/abs/2003.10118). Source-specific details
about all accepted input representations remain reviewer evidence, not a root-
verified universal exclusion. Novelty is unknown.

Verdict: retain as a high-risk conditional reformulation, lower priority until
a concrete compact quotient/extraction algorithm is specified. Do not fund broad
surface infrastructure or declare the coordinate direction impossible. The next
main-problem experiment remains A1's bounded EDS diagnostic; verified gain NONE.
