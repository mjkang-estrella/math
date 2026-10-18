# Higher-corank exploration: full matrix result unproved

This is pre-freeze exploration, not a replacement of any earlier frozen scope, a candidate, or an independent review. The motivating full question is: for every fixed p∈(0,1), every fixed integer k≥2, and symmetric n×n random sign matrices with independent p-biased entries on and above the diagonal, does P(corank≥k)^(1/n) tend to p^(k+1)+(1−p)^(k+1)? No target freeze is asserted, and no upper bound at this rate has been proved here.

## Lower event and exact new support

Let r=k+1 and q=1−p. Requiring the first r rows to agree has probability

    [p^(r(r+1)/2)+q^(r(r+1)/2)] [p^r+q^r]^(n−r).

The symmetric r×r corner must be constant; each outside coordinate independently has r equal signs. This event forces corank at least k. It supplies the claimed liminf only and is a routine antecedent, not a nominee.

section-lemma.md proves the sharp homogeneous codimension-k sign-cube mass bound, classifies equality when p≠1/2, and gives a nonoptimal positive uniform gap away from those equality subspaces. It uses circuit contraction and pays conditional affine fibers directly. The parent suggested circuit/matroid reduction and checked the derivation author-side. Neither action is independent review. Exact finite diagnostics cover74106 rank2 constraint pairs with coefficients{-1,0,1}, n4/5/6 and biases1/10,1/4,2/5,1/2; they do not establish the all-real/all-dimensional theorem.

## The unpaid symmetric interface

The actual biased source239 introduction and complete §§5–6 were read. Its static estimate gives subexponentially many admissible columns when W2 is small; its terminal-window alternative supplies two rare-column costs to control W2-large exceptions. The retained-lattice/cube bound prices each rare column at q^(n−o(n)) after reducing p≤1/2. Thus the exceptional probability has base q². For k=2 and p=.1, q²=.81 exceeds f(3)=.73. Merely repeating the singularity theorem or changing a tail index does not pay the sharper rate.

A prospective route is joint exposure of the anchor row and the two exceptional columns. Triple equality has homogeneous codimension2 per-row mass f(3); conditioning on the anchor discards that structure and leaves only worst-atom q² pricing. But the source's retained-lattice lists depend on the earlier matrix, and transformed bit biases depend on the anchor signs. No proof is given that these adaptive fibers carry a fixed homogeneous codimension2 constraint. The section lemma is applicable only after such an interface, or an equivalent joint entropy estimate, is proved. It does not create that interface.

Similarly, treating a rank-k kernel as fixed and multiplying its section mass over rows is invalid: the kernel is selected from the random matrix and symmetric rows are dependent. A union over all subspaces is not supplied by the lemma.

## Primary operations and history

Jain–Sah–Sawhney2103.02467v1, actual introduction, §2.3 proof and §2.4 statement/remark (extracted1–365), predicts the same nonzero-atom collision base in Conjecture1.2 for nonsymmetric finite-support matrices. Their affine small-ball Lemma2.5, restricted-invertibility/Rogozin construction, compressible-kernel net and incompressible threshold dichotomy are credited. Their q^(kn) cost is not the desired f(k+1)^n cost for biased signs; for p=.1,k2 it is .81^n, not .73^n. The exact homogeneous atom lemma alone therefore does not resolve that nonsymmetric conjecture either.

Singhal1912.02886v2, introduction and entire §2 (extracted1–334), proves the optimal scalar concentration at fixed number of nonzero coefficients is attained by ±1 coefficients, via positive/negative subset-sum profiles and a convex decomposition into pure profiles. This is a scalar arbitrary-center statement and includes the paid biased Littlewood–Offord context. It is not silently reinterpreted as an arbitrary-codimension homogeneous section theorem. Later Fourier asymptotics were not read. Bounded searches did not find an exact section-theorem match; no priority claim follows.

Actual r50 checkpoint/operation ledger and parent principal-compression note were read. Its deterministic-diagonal/loopless-adjacency rate is technical and is not renamed here. I132/I135 are only known through that ledger as the prefactor/classification predecessor; their complete actual files have not yet been read, so comprehensive history eligibility is not cleared. The two canonical239 companions have26non-PDF blobs authenticated; the uniform companion's bodies were not newly semantically read. No full source-probability audit is claimed or required under the stipulated truth rule.

## Disposition

No nominee, no frozen full scope, no proof/contribution gate requested. The homogeneous section lemma is retained as author support; its short circuit proof and lack of essential pinned-source dependence do not by themselves clear the substantial-result expectation. The full random-matrix bridge remains unpaid. All source and primary bodies remain private.
