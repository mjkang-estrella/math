# Exact remaining gaps — zero credit

`no_cubic_8circulant_nut` DOES NOT EXIST in this packet. `Nut8.Target` is a
proposition definition only, not an inhabitant or proof. Nothing here settles
MathDB 365943. The partial proof packet must not be accepted as a solution.

The shortest remaining decomposition after the proved lemmas is:

1. Global labelling: combine `labelOrbit` with representatives of the quotient
   `Quotient (orbitSetoid sigma)` and its cardinality 8 to construct
   V ≃ Fin 8 × ZMod m, with sigma acting by translation. Local orbit labelling,
   positive common size, common period, and exact local period divisibility are
   already proved. The equivalence with the source's existential CYCLIC SUBGROUP
   definition is ordinary via a generator; there is no Lean subgroup/zpowers
   action bridge beyond the literally integer-power orbit definition.
2. Build the signed Fourier quotient C. `nut_sign_character` already proves
   adjacency-kernel invariance, a scalar action and the ±1/parity assertion.
   The coordinate character formula, symmetry, C u = 0, linear injective kernel
   lift, and nullity-one transfer are still unproved. Do not substitute an
   abstract lift hypothesis for these graph-specific constructions.
3. Prove connectivity of a nut graph and quotient connectivity; pair internal
   shifts b and -b, establish the shared semi-edge sign, and exclude opposite
   signs on double edges using fullness. Obtain the precise admissible matrix
   grammar. Connectedness at eight vertices excludes diagonal weight 3 and
   off-diagonal weight 3. These local and connectivity proofs are not formalized.
4. Prove a complete symmetry-reduced generator: connected subcubic underlying
   graphs, multiplicity/diagonal augmentation, switching along a spanning tree,
   shared semi-edge sign, and the trivial-character pretest. The inherited
   catalogue has 194 underlying graphs and 669 augmentations. Its final 7,176
   matrices represent only 551 distinct absolute matrices. Therefore checking
   these certificates alone also misses the unsigned-pretest exclusions unless
   those exclusions are formally supplied. No isomorphism/canonicalization or
   BFS-normal completeness theorem has been proved. This is the main bottleneck.
5. Prove executable determinant correctness and the symmetric rank/nullity/
   diagonal-cofactor support lemma over R, then check ALL cases and compose.
   `CertificateBench.detFuel` is only a list computation with two checked
   sample values. It has NO proved relationship to `Matrix.det`, and it is
   NOT a verified graph obstruction. No general adjugate lemma is supplied.
6. Prove the literal endpoint, repeat the entire strict replay/audit with all
   added declarations, and obtain independent root acceptance. The bounded
   prior-art limitations in PRIOR-ART.md also remain to be reconciled by root.

## Counts and kernel-cost evidence

Before committing to a brute-force generator, scripts/count_cases.py counts
15,304,856 labelled unsigned symmetric matrices and 14,156,673,552 labelled
signed matrices with fixed positive semi-edge sign, absolute row sum 3, and
entry magnitudes at most 2. These counts include disconnected matrices and
omit the unsigned pretest, so are upper search spaces, not surviving cases.
Allowing a negative common semi-edge sign gives at most twice that count.
The DP is an ordinary Python estimate, not a Lean completeness theorem.

A dense recursive list Laplace computation of two samples was killed at the
6 GiB sampled private-memory threshold after 19.38 seconds (bench-01 receipt).
A sparse zero-skipping version checked one determinant 48 and one principal
minor 0 in 1.26 seconds, sampled peak 2,303,082,496 bytes, including Lean startup.
Both use `decide +kernel`, never native evaluation. A rough extrapolation of
two samples per module is 3,588 modules, about 75 minutes of rebuild startup
and checking at that measured rate, before completeness and linear algebra.
This is NOT a reliable upper bound: the sample is small and sparse, proofs of
checker correctness may change cost, and individual hardest cases are untested.
The 7,176-certificate route is computationally plausible only after a verified
canonical/switching reduction; direct 14-billion-case enumeration is unsuitable.

No finite obstruction theorem is claimed, even conditionally as a Lean endpoint.
