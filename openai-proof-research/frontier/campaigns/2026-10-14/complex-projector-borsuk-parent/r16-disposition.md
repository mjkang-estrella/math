# Parent disposition: B8C complex projector-plane cover

**FULL_B8C_PROOF_CANDIDATE_REVIEW_REQUIRED.** Counted=false, campaign4/10.
Frozen scope133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838.
Author seal fc997d93ac553767e1ce252e73e57ffb3c675d36b09d1949c1e8a14f6f9db9af (416 bytes).

The full target is diam(X)=sqrt(2) and b(X)=9 for all complex rank-one orthogonal projectors in Herm₃'s trace-one hyperplane, R⁸. Nine actual smaller-diameter sets must cover all X; no eight-set cover is possible even with arbitrary nonmeasurable sets. This confirms Borsuk's d+1 value for this X, not a counterexample in dimension eight.

Parent read the entire candidate, frozen scope, source contracts, status, verifier and provenance records. Parent read the actual pinned real-projector theorem, full positive/signed extension proofs and the topological label-bound statement/proof. The source concerns real projectors in R⁹; its theorems do not directly assert the complex result. Candidate re-proves the continuous Hermitian lower-bound construction; the same method is credited as antecedent.

The proposed lower bound enlarges arbitrary strict-gap covering sets to open sets, builds a continuous partition of unity, integrates a homogeneous extension over the complex unit sphere, and takes positive/negative spectral parts. Orthogonal ranges have disjoint coordinate supports, producing an odd nonvanishing map S⁸→S^(m−1), hence m≥9.

The proposed upper bound starts from the nine Hesse SIC vectors. Their maximum squared overlap is at least1/2, equal only at twelve MUB rays. Plain closed Voronoi cells contain orthogonal boundary pairs and do not solve the strict-diameter cover. The new operation orients each orthonormal triple cyclically, assigns a favored pole to each Hesse line, and uses the Weyl–Heisenberg orbit of one perturbed fiducial. Its favorable first derivatives have a common positive lower bound. A two-trio local estimate at each hole, followed by compactness away from holes, is intended to raise the maximum overlap strictly above1/2 everywhere. Bessel plus compactness of each closed cell then gives strictly smaller diameter.

Required independent review:
B1. Re-prove the lower bound for arbitrary sets: open enlargement, support identity at singular PSD matrices, absence of cancellation, odd-sphere dimensions and Borsuk–Ulam. Do not impose smoothness/measurability on original covers.
B2. Verify all Hesse/MUB formulas, all twelve holes and equality cases, phase conventions, orbit covariance and cyclic favored-pole assignments. Candidate section3 mistakenly says “nine holes” before correctly listing twelve; fix in a future revision, not silently in frozen bytes.
B3. Check κ(s,h), the simultaneous four-positive-direction fiducial, and the local two-trio overlap expansion with complex conjugations. The estimate must hold for all complex z₂,z₃ in the stated neighborhood, including directions where the favored trio's first-order spatial term vanishes. Recompute the r and ε constants symbolically; sampled descents are not evidence of a universal cover.
B4. Check passage from local neighborhoods to a common positive ε on the compact complement, including any empty-complement convention, uniform perturbation norm bound, closed Voronoi coverage and strictly smaller diameters. Existence is the frozen target; an explicit far-region margin is not required if the compactness argument is valid.
B5. Assess contribution independently against actual primary complex-projective covering, Hesse SIC/MUB and perturbation literature. The author's search was thin: Kalai survey portions were read, but the CP² SIC classification paper was seen only as a search result. No priority or substantiality claim is established. The Hermitian extension is a routine transfer of the source method; substantiality, if any, must reside in the strict nine-center cover and its hole resolution, not the dimension label alone.

Parent integrity: exact35files/8directories including root, sizes/hashes, safe unique paths and no symlinks checked independently before guarded execution. All14 pinned blobs matched the complete live catalogue. Correct anchor passes; wrong anchor rejects. All42observed files (35owned+4fixed source/context+1original parent brief+2mutable ledger/task observations) unchanged during replay. See r16-verification.json. No floating-point diagnostic was rerun or used to infer the theorem.

Provenance clarification: the child calls its brief snapshot a transcription “with no repository original.” An original exists at linear-ryser-parent/fresh-r16-brief.txt; the parent's audit records its digest. Do not describe the transcription as byte-identical. The review must use the original parent's brief as historical context. Mutable tasks legitimately changed during child work and are not mathematical inputs.

Next: independent full B8C proof and separate contribution review, with all original active instructions, exact full-history reference, author findings and B1–B5. No manuscript, Lean implementation or acceptance yet. PCW and crossing review remain separate.
