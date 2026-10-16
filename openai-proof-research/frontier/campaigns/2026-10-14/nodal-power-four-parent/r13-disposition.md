# Parent disposition: nodal power excess in dimension four

Status: **FULL_T4_PROOF_CANDIDATE_REVIEW_REQUIRED**. No mathematical PASS, novelty PASS, acceptance or publication. New-ten count remains **4/10**.

The Factory/Opus 5.5 analytic round 13 returned a full proof candidate for one smooth metric on the closed connected manifold S³ × S¹, a fixed ε₀ > 0 and real smooth Laplace eigenfunctions with λⱼ → ∞ such that H³(Z(uⱼ))/λⱼ^(1/2+ε₀) → ∞. The fixed exponent and fixed metric are essential. Qualitative unbounded excess or a frequency-dependent metric would not resolve T4.

Frozen scope SHA-256: 3348c130c424d6f753a39c6529cff81c0d923c3bb8d1eeb395327abb6734dc0f.
Externally reported seal SHA-256: 056fc8c98bbdcd01a701ed94db722bcba07a9ea983e4c4459be34f875abfa657.
Candidate SHA-256: 2775917ef598b09507fbc217054e4ca8c65a8e377774bea3214929886ab7aab7.
Pinned upstream: openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## What was checked

Parent read the full 851-line candidate, source-contracts, literature screen, status, verifier and manifests. Parent additionally read actual power-paper main theorem and framework/step, the dimension-dependent intersection in envelopes.tex, the dimension-three/four companion main statements, and the companion preparation proof. The source power theorem is on S⁴ × S¹; the companion claims qualitative excess but no fixed positive power in dimensions three/four. The source preparation uses a first integral and gives mass fraction p_h/8; its threshold depends on the fixed profile. Parent has not independently reconstructed every waves/global calculation. No mathematical PASS follows from the parent reading.

Independent authentication checked exact membership of **50 files and 12 directories including root**, no symlinks, safe nonduplicate paths, all bound sizes/hashes, scope, and **31 pinned Git blobs** against the complete live catalog. Guarded replay returned exit 0 (134 positive lines); wrong anchor returned exit 1. All **55 observed files** (50 candidate + 4 fixed external + mutable live ledger) were unchanged during both runs. See r13-verification.json and verify_frozen_r13.py. This is integrity evidence only.

The candidate verifier calls itself fail-closed, but its external anchor is optional, is checked after payload manifests, and --pre-seal bypasses it. It is not independently adequate as an authentication-first boundary. Parent authenticated everything before executing the inspected code under a write/process/network-denying audit hook. Review packages should use a required external anchor, authenticate manifests before reading payload, reject noncanonical/duplicate paths and symlinks, and use internal context snapshots so ordinary ledger updates do not invalidate a frozen review.

## Mathematical response and unresolved review obligations

P1. The new operation is quantitative preparation (Lemma 6.1) on a fraction approaching one of the gradient mass, using a frozen affine frame and an asymmetric periodic second derivative. Establish uniformity using only the allowed C¹ metric bounds; no hidden higher metric derivative modulus may enter the common exponent. Check the S ≤ ν device, control of Christoffel terms, preservation of the favorable direction where H'' is negative, and the Schur complement estimates.

P2. Verify the order of all constants without circular dependence: radial pattern and mass gain first, weak thresholds, κ, preparation amplitude/thresholds, ν, then fixed ratio r = ν⁶. Confirm grid losses and weighted mass estimates, regularity of the periodic disk pattern at center/boundary, and that full preparation on almost all mass really pays the subsequent corrugation loss.

P3. Reconstruct Lemmas 5–8, including old third derivatives, child-scale bounds and lower favorable margins at all points, supports and boundaries. Check first generation and inactive regions. The logarithmic number of generations must yield one positive γ independent of derivative order and input-pair accuracy, with the advertised derivative exponents.

P4. Section 9 is part of the proof, not a cited theorem on S³: source [P] is on S⁴. Independently transfer every needed phase, packet, gluing, elliptic correction, simplicity and diagonal argument to base dimension three. In particular reconstruct the stated rank-four jets from the six packet parameters, fourth-dimensional small-ball density/grid exponents, three-dimensional certificate area and Sobolev estimates, round eigenvalue N(N+2), all collar requirements, and the one fixed smooth limiting metric. The author explicitly did not rewrite waves.tex 282–494 and 531–708. A claim of dimension-genericity alone does not clear these steps.

P5. Review contribution separately. The target is stronger than the companion conclusions, but Lemma 6.1 resembles the companion preparation operation. Determine whether the quantitative invariant and fixed-ratio iteration are substantial new work or a routine quantitative recombination. The author's external literature screen is limited: secondary ProofAtlas reading and several primary abstracts/listings, not a comprehensive primary-body comparison. Read relevant primary bodies and record exact overlap; neither no search hit nor the target's strong appearance establishes novelty.

If any critical step is unpaid, return precise FAIL/UNRESOLVED for full T4. A corrected local lemma or a qualitative special case is not a full PASS. Do not edit the frozen candidate. Proposed repairs belong in the separate review with their status made explicit, for a later author revision and fresh review.

## Next action

Delegate one independent GPT-6.1-Sol/high/default review with separate mathematical and contribution verdicts. Include the original discovery brief, all candidate findings and this response. No nested delegation, manuscript, Lean package, count increment, external publication or submission at this stage. Crossing-number manuscript review and full linear-Ryser round 2 remain separate work.
