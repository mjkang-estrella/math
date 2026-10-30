# r35: structured interpolation screen; no full resolution

Status: UNRESOLVED / NO NOMINATION. Credit 0. Root owns acceptance; 5 additional / 35 total unchanged. No Lean was written or run.

## Screening and source scope

Read root/batch AGENTS, ledger.json, prior-campaign-context.json, NEXT.md and recent root r32/r33/r34 handback ADOPTION.json records. The ledger and explicit assignment exclusions govern; no previously credited family, polyomino route or held BBG target was pursued.

Four live AIM entries were fetched before selecting an attack:

* 554, fixed-interval absolute minimax approximation of x^(-gamma), numerator degree n-1 and denominator degree n: rejected immediately on actual public main theorem, not merely its solved badge. Kaiwen Jin's 13 October manuscript, Theorem `thm:main`, has exactly the interval, fixed exponent, unrestricted outside poles and proposed constant. `sources/stieltjes-proof.tex` contains the statement and body. No audit of that proof is claimed.
* 597, prescribed-flux entropy chain rule under only finite kinetic action and Fisher information on every bounded Lipschitz domain: rejected on the actual public manuscript's chain-rule theorem and assumptions. `sources/entropy-proof.tex` explicitly allows vacuum, the prescribed flux and nonsmooth nonconvex domains. No audit of that proof is claimed.
* 569, all-degree sqrt(2) Galerkin-to-componentwise-projection bound on every nonobtuse triangle, with no minimum-angle bound: actual latest arXiv v1 body read, Section 2.2 and the unnumbered Conjecture at the end, equations (1.3)/(2.1), and the curl-based auxiliary forms. A bounded-degree matrix does not establish all p or arbitrarily thin triangles. The source's own degree-independent stability has a shape-dependent constant. No complete mechanism was established; deferred rather than recasting it as another universal spectral problem. The catalogue's Conjecture 2.5 numbering refers to the published version; it is unnumbered in the read preprint. Published body not independently read.
* 641, Bos's fixed quartic simplex nodes: chosen for an explicitly algebraic determinant attack. The cubic assertion is already covered by Sadeghi's 4 October public proof (`sources/bos-cubic-proof.tex`, main theorem); its abstract expressly excludes all three quartic targets. Not a quartic proof. Current clopen OP-00333 is only a lead, and is less precise than AIM about the cubic status.

Exact immutable AIM URLs and all retrieval hashes/times are in http.json. Open labels/empty database arrays are not used as novelty evidence.

## Literal selected target

Bos, *On Fekete Points for a Real Simplex*, arXiv:2205.06498v1, submitted 13 May 2022 08:08:51 UTC; abs page lists only v1. Section 4, pp12–16, gives the quartic nodes and Conjectures 4.2, 4.3, 4.6. Journal citation is Indagationes Mathematicae34(2)(2023),274–293, DOI10.1016/j.indag.2022.11.003. DOI endpoint returned a redirect shell; actual publisher article returned403 and was not retried/bypassed. Exact journal/preprint comparison remains unperformed. Actual preprint PDF and HTML were body-read, including Definitions0.1–0.4, Propositions0.5–0.6 and proofs, Remark0.7, Section4 and the degree5 determinant factorization in Section5.

For each d>=1 and every nondegenerate real d-simplex, F4 consists of all distinct barycentric permutations of
(1), (1/2,1/2), (s,1-s), (a,b,b), (1/4,1/4,1/4,1/4),
appending zeros, where s=(1+sqrt(3/7))/2, a=(4+sqrt5)/11, b=(7-sqrt5)/22. Types with more than d+1 coordinates are omitted. There are N=binomial(d+4,4) nodes. Conjecture4.3 says their absolute degree4 Vandermonde determinant is at least that of EVERY N-point configuration in the simplex, for any one fixed polynomial basis. It is not restricted to symmetric competitors, boundary nodes or fixed face incidences.

The other surviving targets are Conjecture4.2 (sum of cardinal squares <=1 on the whole three-simplex) and4.6 (sum of cardinal fourth powers <=1 for all dimensions). No result on any of these three is nominated. In particular the already-published dimension4 centroid square-sum violation is NOT a new refutation of4.3 or4.6.

## Mathematical attack and failed bridges

See FAILED-ROUTES.md for complete ordinary arguments, including the literal cardinal-polynomial and determinant bridges. These are obstructions to our methods, not discoveries submitted for credit:

1. Keeping each node within its original supporting face gives a block-triangular homogeneous-monomial Vandermonde. All blocks have size at most3 except scalar centroid blocks. The known degree4 Fekete property in dimensions1/2, and AM–GM for each four-coordinate block, show no such perturbation improves the determinant in ANY dimension. This is a routine constrained consequence of the published low-dimensional case, not a new full theorem.
2. Moving all four-face centroids the SAME fraction toward the global centroid genuinely enters the full simplex interior for positive fraction and d>=4. Its exact determinant ratio is a Gram-kernel determinant. Positive semidefiniteness plus Hadamard bounds it by1 for every d and fraction in[0,1]. This closes a plausible interior refutation family without substituting finite diagnostics for an all-dimensional proof.
3. The published centroid square-sum violation does improve a probability-weighted Gram determinant. The explicit determinant-lemma bridge shows why it does not produce an N-point equally weighted competitor: the improved measure has N+1 support points and unequal weights. The Kiefer–Wolfowitz theorem quoted/proved around the source's Propositions0.5/0.6 cannot be reversed to infer failure of the fixed-node Fekete claim; Remark0.7 explicitly distinguishes the notions.

No broad random search or optimization census was conducted. Sixteen small exact rational determinant checks and one exact weighted-design check validate the obstruction formulas only. No finite affirmative result is promoted to a source theorem.

## Closest bodies, followups and limits

The closest actual body is Bos's own2022 paper: quartic explicit cardinal polynomials, low-dimensional Fejer theorem, four-dimensional centroid calculation, and existing degree-elevation proof strategy. Section5 explicitly references Bos1991 for Vandermonde factorization. The 1991 primary publisher abstract was located (DOI10.1016/0021-9045(91)90063-G); its full body was NOT read. No claim of novelty for face factorization, Gram kernels, Hadamard, the determinant lemma or the contraction obstruction is made.

Targeted public searches for Bos Conj4.3, quartic Fejer proof and exact title plus2024/2025/2026 returned the source, the partial public cubic resolution and unrelated interpolation papers, not an identified full quartic resolution. A guessed university author-page endpoint returned an application-error page despite HTTP200; no complete author bibliography was obtained. This is an author-followup coverage limitation, not clearance. No claim of exhaustive citing-literature, MathSciNet/zbMATH or worldwide priority.

Live proof registries were screened early. Omega dev advanced21 commits from r34 to cf6f598e7c818a4e9a7583b51f3d717f1466c1d6, latest11:26:45UTC, with133 reported changed files, below the300-file cap and all21 commits returned. Relevant complete D5/Problems baseline scopes were reconciled with this reported delta; neither whole-dev coverage nor a whole-dev complete tree is asserted. AIM, OpenAI main and Count heads unchanged. Actual public cubic/Stieltjes/entropy theorem bodies and the unrelated Omega Fekete-lemniscate problem body were read, not just path badges. See registry-screen.json. This is no novelty PASS.

## Strongest objection and next falsifier

The obstruction is narrow: arbitrary competitors can change face incidences, move multiple node types inward by different amounts, or break symmetry. The symmetric Gram matrix proof then need not apply. An exact N-by-N cardinal-value determinant with absolute value>1 at genuine simplex points would refute Conjecture4.3. A proof needs to control ALL such configurations; none is supplied. A quartic Fejer proof in dimension3 would resolve4.2 but not the all-dimensional quartic question. Merely repeating the source's dimension-by-dimension coefficient checks is not a proposed new mechanism.

Lean feasibility: exact algebraic-field arithmetic and finite determinant certificates would be practical if an exact counterexample existed; a universal proof requires the missing global comparison first. No helper Lean, large formal investment, paper or acceptance packet is justified. Independent root review is required before any such investment.
