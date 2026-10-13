# I291 — independent proof gate for I287

**Main theorem: PASS. Original boundary certificate: PASS. Optional scalar-polynomial corollary: PASS with its credited external dependency. No necessary repair.**

The original target was read fully, all 288 lines, and authenticated at both the working-tree path and frozen commit `8c9e63ee`: SHA-256 `8f8eb9a51203ec949356a1e92913447b56766e68496ec2384003c24430bbcd0b`. It was not modified. The [independent derivations](../experiments/i291_crouzeix_counterexample_proof/analysis.md) expand and verify the original proof rather than substitute a corrected target.

The explicit six-dimensional (N) is unitarily irreducible, has (N^4=0), and has unit-disk numerical range. Every support pencil has eigenvalues (1,1,-1,-1,\sqrt7/8,-\sqrt7/8). Circle unitarity and the maximum principle give (\max_{W(N)}\|P\|=1). The base-first evaluation has squared singular values (4,337/128,337/128,(569\pm33\sqrt{113})/512) and seven zeros. Its unique top input and output lines are the displayed Schmidt-rank-two pair, and its exact complementary squared norm is (337/128).

Complex product vectors have squared overlap at most one half with the top input. Therefore every constant complex unit coefficient compression satisfies (\|(v^*Pu)(N)\|\le\sqrt{849}/16<2). This proves the specified-witness counterexample to an unrestricted extension of R016. It does not contradict R016's base-dimension-at-most-four theorem or disprove disk rigidity.

The boundary certificate uses the **original** mass-two resolvent field. Direct congruence proves positivity and rank four everywhere. The cross block is unitary, (\Delta J\Delta=0), and the trace identity yields (H^{1/2}DH^{1/2}=0). Both coefficient ranks are two, (D) has inertia ((2,2,2)), and every direct-source residual is exactly zero. Actual pinned source operations and their normalization were inspected; the companion's similar-matrix density was not substituted.

Section 10 is separate: the exact norms of (N,N^2,N^3) are correct and strictly below two. The actual [ACV v3 Proposition 11.1](https://arxiv.org/html/2608.27346v3#S11), including its proof and supporting Proposition 10.1 scope, supplies the credited scalar polynomial implication. Thus each nonzero scalar polynomial separately misses equality. The polynomial implication does not exclude nonpolynomial Schur-jet extremizers, and no strict scalar spectral supremum below two is inferred.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were stipulated true. Independent package-free rational-radical checks passed, including all Laurent coefficients of (HDH=0); no numerical sampling or scan was used. Exact reading scopes and provenance are in [reading-and-failures.md](../experiments/i291_crouzeix_counterexample_proof/reading-and-failures.md), [literature.md](../sources/i291_crouzeix_counterexample_proof/literature.md), and [input-authentication.json](../experiments/i291_crouzeix_counterexample_proof/input-authentication.json).

The LSS base matrix and disk geometry are credited prior art. This proof gate makes no contribution acceptance, smallest-dimension claim, full size-six classification, nondisk example, near-extremizer theorem, or worldwide priority claim. No shared index was edited. The supplied twelve accepted findings remain twelve; output hashes are returned detached.
