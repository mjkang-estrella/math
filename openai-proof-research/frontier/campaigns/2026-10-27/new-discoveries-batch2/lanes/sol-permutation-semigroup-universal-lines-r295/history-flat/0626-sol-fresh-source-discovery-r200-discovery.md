# Scope and source

Research only in r200, solo. No shared edits, git, external messages/posts/uploads, MathDB edits, browser, Lean or manuscript investment. The four required root handbacks were read first, after the ancestor/batch rules and administrative ledgers. Their decisions were preserved as assigned-input copies. In particular sparse terminal reliability remains under independent review; no reuse of that result or the excluded Robin, higher convex-order, clustering, cosine, Brownian, DSBS, pendulum or coverage targets occurs here.

Primary: https://arxiv.org/html/2610.17393v1, Małgorzata M. Czerwińska, Jose A. Franco, Allan Merino, *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. The unversioned abstract https://arxiv.org/abs/2610.17393 reports only v1, submitted 12 October 2026 at 20:57:57 UTC. DOI alias 10.48550/arXiv.2610.17393. Retrieved 2026-10-30 UTC, exact times and body hashes in http.jsonl. This date comes from the execution clock, rather than the environment's initial calendar date. No separate journal version is asserted. The arXiv HTML full body, its extracted text, and abstract bytes are retained and copied; mathematical statements were read from the full body, not the abstract.

## Literal question and quantifiers

For every positive integer n and real-valued function f on (0,infinity), define f(A) by finite-dimensional spectral calculus and d_f(A,B)=||f(A)-f(B)||_F. Radial convexity of order n means that **for every triple of positive definite Hermitian n-by-n matrices A,C,B with A<=C<=B**, both d_f(A,C)<=d_f(A,B) and d_f(C,B)<=d_f(A,B). The definition does not require d_f to separate points (Definition 1.1, Remark 1.2).

Conjecture 4.10 states that radial convexity of order n holds if and only if f is matrix monotone of degree n. The latter allows either a single globally increasing direction f(A)<=f(B) for all A<=B, or a single globally decreasing direction. Direction is not chosen separately for each pair. Constants satisfy the non-strict statements. The printed conjecture imposes no explicit differentiability assumption, while Theorems 4.11 and 5.4 do. A differentiable-only result would therefore leave a regularity/scope issue to resolve; that issue is not counted as a new result. The proposed route below assumes C1 regularity and does not silently fill this gap.

Actual source bodies read: Definitions 1.1, 2.3, 2.9 and 2.15; the Loewner characterization and Remark 2.17; Proposition 3.9 and proof; Propositions 4.1, 4.3, 4.5, 4.8 and their proofs; Conjecture 4.10; Theorem 4.11 and proof; Remarks 4.12–4.16 including Proposition 4.14 and proof; Proposition 5.1 and Theorem 5.4 with proofs. Introduction and concluding scope were also read. The source provides n=2, all unitarily invariant norms in the differentiable setting, not a higher-order converse. Its order-two-to-three and order-three-to-four examples fail radial convexity at the larger size and cannot refute the conjecture.

## Full applicable classical bridge: the known direction

Suppose f is matrix monotone increasing of the fixed degree n. Given any A<=C<=B, put U=f(C)-f(A) and V=f(B)-f(C). Both are PSD, and tr(UV)>=0 because tr(UV)=tr(U^(1/2)VU^(1/2)). Thus

    ||U+V||_F^2 = ||U||_F^2 + 2 tr(UV) + ||V||_F^2

dominates both ||U||_F^2 and ||V||_F^2. Taking square roots gives exactly both radial inequalities. If f is decreasing replace it by -f, which leaves d_f unchanged. This proves the whole forward implication, all triples and all finite n. It is Proposition 3.9's classical mechanism and receives no novelty credit. Shortness by itself supplies no objection to the remaining converse.

For C1 f, diagonalize A=diag(lambda_i); the derivative T_A=Df(A) is the real self-adjoint Schur multiplier with Loewner matrix L_ij=f[1](lambda_i,lambda_j), diagonal f'(lambda_i). Loewner's fixed-degree criterion says that L>=0 for every node tuple is equivalent to increasing matrix monotonicity of that same degree. This criterion does not allow replacing L by its Hadamard square.

Radial convexity gives ||T_A(X)||_F<=||T_A(X+sY)||_F for every X,Y>=0 and s>=0 by taking the first small matrix increment. Expansion and then s down to zero give <T_A(X),T_A(Y)>_F>=0. Schur self-adjointness rewrites this as tr(X ((L o L) o Y))>=0. Testing rank-one X and then Y=J proves L o L>=0. Conversely Schur positivity proves this derivative-inner-product condition. These are the exact source Propositions 4.5 and 4.8, only necessary for global radial convexity. In degree two the determinant factorization and common scalar derivative sign recover L (or -L). No such general inference has been proved here in higher degrees.

## Sustained all-order route and exact missing step

Global radial convexity is stronger than the same-base derivative condition. For any ordered pair A<=B, set Z=f(B)-f(A), and let H>=0. For sufficiently small t>=0, A-tH remains positive definite. The chain A-tH<=A<=B implies

    ||Z||_F^2 <= ||f(B)-f(A-tH)||_F^2.

The right derivative at t=0 is 2 tr(Z T_A(H)), so this trace is nonnegative for every H>=0. By self-adjointness and self-duality of the PSD cone this is equivalent to

    T_A(f(B)-f(A)) >= 0.                       (G1)

Similarly A<=B<=B+tH gives

    T_B(f(B)-f(A)) >= 0.                       (G2)

Unitary covariance makes these statements basis independent. These necessary conditions hold for all sizes under consideration, all positive definite ordered pairs, and every C1 f satisfying the radial premise; no finite sampling is used in their derivation. Replacing f by -f leaves both composites unchanged, so scalar monotonicity must first fix direction.

The plausible mechanism is to use (G1) and (G2) with all finite rank-one ordered perturbations, including endpoints approaching the boundary, to recover positivity of T_A itself. **Missing uniform lemma:** for increasing C1 f on the entire positive half-line, with radial convexity at the fixed size n and hence (G1),(G2) for every ordered pair, prove T_A(H)>=0 for every A>0 and H>=0. Even the stronger proposal that scalar monotonicity plus (G1),(G2) alone suffice is not established. No limit to a boundary is taken without control of f there; it may have finite or infinite one-sided limits. No assertion that the image differences f(B)-f(A) fill the PSD cone is justified. This is the central residual quantifier, for every n>=3, and it cannot be discharged by finite determinant tests. Regularity from the literal conjecture's arbitrary-f premise remains separate. There is no full ordinary candidate.

## One exact obstruction control

checks.py uses rational arithmetic for

    L = [[1,19/20,1/2],[19/20,1,1/20],[1/2,1/20,1]].

Every entry is positive, all 1-by-1 and 2-by-2 principal minors are positive, det(L)<0, while every principal minor of L o L is strictly positive. Its off-diagonal entries are also consistent with secants at nodes 1,2,3 and values 0,19/20,1. Thus positivity of entries and the elementary secant averaging relation do not repair the pointwise square-root argument. The test makes **no** global claim about existence of a radially convex f with those data. In particular it is not a counterexample to Conjecture 4.10, nor does it establish that a globally 2-monotone function realizes those jets. It only rules out a proposed insufficient matrix inference. No grid or parameter scan was run.

## Closest-body comparison and chronology

Hansen–Ji–Tomiyama, *Gaps between classes of matrix monotone functions*, arXiv:math/0204204v1 (16 April 2002), DOI 10.1112/S0024609303002455; journal BLMS36(1)(2004)53–58. The full eight-page preprint body was read, particularly Lemma 1, Theorem 2 and proof, Proposition 3, and Corollary 4. Its truncated odd series g_n has positive Hankel matrix near zero, but its next-order Hankel matrix has a 3-by-3 principal determinant -(2n-1)^(-3). Fractional-linear order isomorphisms transfer the gap to a half-line. This proves finite-degree gaps; it does not prove radial convexity at the failing degree. Invoking it as a refutation of the source would omit exactly that premise. The 2004 typeset body was not separately authenticated; no discrepancy-free version comparison is claimed.

Audenaert, *In-betweenness: a geometric monotonicity property for operator means*, arXiv:1011.6313v1 (29 November 2010); DOI 10.1016/j.laa.2011.02.051; journal LAA438(4)(2013)1769–1778. Primary preprint introduction, Definitions 1–6, Kubo–Ando integral representation, and Section 6 including Theorem 5 and proof were read. The proof reduces by congruence to I,C in the congruence-invariant trace metric and applies scalar betweenness and the log norm. This is a full bridge for the stated metric/mean result, not the present fixed-n converse for arbitrary f and ordinary Frobenius pullback distance. Ordinary Frobenius pullback distance has no general congruence invariance, and no representing Kubo–Ando mean can be assumed before operator monotonicity. The retained PDF bears an internal footer '13 May 2022' despite its v1 header; this chronology anomaly is retained, not silently resolved. No publisher-body identity is asserted.

Efe A. Ok, *Order-preserving extensions of Lipschitz maps*, DOI 10.1017/S1446788724000120. Actual Cambridge full HTML body was accessible, with metadata online 17 December 2024 and February 2025 publication. Definitions (2-1)–(2-3), examples distinguishing radial convexity from stronger radiality, Theorems 3.1 and 3.4 with proofs were read from the final freeze. The extension proof constructs overlapping order/Lipschitz scalar intervals and uses maximal extension. It assumes stronger radiality on partial orders and preserves already order-preserving maps; it does not force arbitrary spectral f to preserve matrix order. The PSD order is not total. Even a valid scalar Lipschitz extension does not identify all quadratic forms of f(A) with those extensions. Therefore no full classical subsumption bridge results. A title search returned the distinct 2026 Gargiulo–Ok Hadamard-space paper, arXiv:2603.03549v1; its downloaded body was not relied on and is not substituted for Ok's cited 2025 paper.

These older results precede the source. The current bounded arXiv exact-phrase screen returned only 2610.17393. It is not a complete public-proof registry screen, and no current GitHub head was authenticated because its routes remain denied. No MathSciNet/zbMATH or exhaustive citing-literature clearance is claimed. The open label is not novelty evidence.

## Reconnaissance and limits

Fei Xue, arXiv:2610.39026v1, rank-two discrete monotonicity, was an alternative geometric reconnaissance lead. Title/author/statement aliases were screened with no hits; the full primary bytes were saved and introduction and Sections 2–3 read. It proves rank at most two and points to a general-rank property. No higher-rank all-order mechanism was established, so it was not invested in or promoted as another fresh slot. No resolution or exclusion claim is made about it.

The corrected prior indexes were reused via the r198 consolidated original-record bindings and frozen r193/r194/r197/r198 index receipts. r198 provenance-qualified alias records were excluded, never promoted by equal bytes alone. New direct lane reports were added without recursively indexing copied histories. Original r111–113 records survive in the freeze. No changed original hashes were found during initial refresh. Scientific reports are point-in-time snapshots of active files, not declarations of eternal immutability. Administrative NEXT/ledger/prior context are snapshots only and excluded from scientific original/copy assertions. Current bounded search cannot clear all history, and historical capped intervals stay parked.

Source reads before primary-copy freezing and the initial inventory command deviation are disclosed in FAILURES.md. Final verification tests the actual frozen pairs and manifest after final writes; it does not retroactively cure those workflow departures. No denied host was retried, proxied or bypassed. Final disposition: fresh unresolved primary target, promising global mechanism with unproved positivity recovery, **zero nominations and zero credit**.
