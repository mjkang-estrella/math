# Independent novelty screen (preliminary), review lane 2026-10-26

## Refetched primary record
- MathDB 351688 refetched fresh from https://mathdb.com/api/posts/351688 (HTTP 200;
  novelty/mathdb-351688-refetch.json): status "open", progress null, and
  solutions / human_solves / model_attempts / formulations / attachments /
  replies / comments ALL empty. Confirms parent; empty record alone is not
  novelty evidence.

## OpenAlex citing corpus (3 papers; full retained texts compared)
- bessel2026 (10.2140/pjm.2026.343.261): cites FS23 once, for a parameter remark
  ([FS23, Section 2]); studies hyperbolically CM densities / ID modified Bessel
  distributions. No derivative-ratio content. No overlap.
- unimodal2408.01755 (10.1007/s00025-025-02431-4): cites FS23 ONLY in the
  bibliography (never in text). Topic: unimodality preservation by ratios. No overlap.
- fox2502.10483 (10.1007/s13540-026-00482-0): no Ferreira/Simon/Mills mention in
  the retained text at all. Positivity of Fox H functions. No overlap.

## Nearest works checked in full bodies
- Yang 2507.10954 section 4.4: proves CM of D_{p[n],q[n]}(x;lambda_n) =
  prod R_{p_j} - lambda prod R_{q_j} (differences of products of Mills moments),
  Proposition 6; log-convexity of p -> R_p(x). These are weighted
  sums/products, NOT quotients -r^2/r'. Does not cite Ferreira-Simon. No overlap.
- Xu-Yang 2026 (10.1186/s13660-026-03505-9, published 2026-06-19), full HTML body
  scanned: 0 occurrences of "Ferreira", "Simon", "2108.09244"; studies
  Y_{a,b}(x) = (x^2+a)R^2 + bxR higher-order monotonicity; its Conjecture 7.1 is
  its own D_n(x,a) question. Different object; no overlap. (Archived fetch of
  the readable body in this session; xuyang2026.html direct curl was blocked,
  166-byte shell.)
- Salazar 2606.31647 "Order-Moment Transport...": gamma-normalized Mills-ratio
  theorem is STP-inf of the Hankel kernel (a,b) -> M_x(a+b+1),
  M_x(p)=R_p(x)/Gamma((p+1)/2) -- total positivity in the ORDER parameter at
  fixed x. Orthogonal axis to Conjecture 3 (fixed n, CM in the argument z).
  No mention of Conjecture 3 or Ferreira-Simon. No subsumption.
- Ferreira-Simon follow-up 2212.07974 (Constructive Approximation 2023): Wright
  function log-concavity; unrelated to Conjecture 3.

## Targeted searches (exa, 8 queries total this session)
No known refutation, proof, or resolution of Ferreira-Simon Conjecture 3 found;
no prior counterexample to CM of -r^2/r' or of -(r^(n))^2/r^(2n+1) located.
Closest classical facts: r itself is CM (Shenton 1954); 1/r convex (Sampford);
Yang-Tian Turan ratios of higher derivatives. None subsumes the conjecture's n=0
case or its refutation.

## Limits (recorded, non-blocking for preliminary screen)
- No MathSciNet / zbMATH access; no absolute-priority claim possible.
- Semantic Scholar deliberately NOT retried (parent recorded HTTP 429).
- Published Trans. AMS body inaccessible (soft block); see
  sources-published/published-version-attempt.md. arXiv v2 confirmed latest
  (v1 2021-08-20, v2 2022-05-19) and is the reviewed text.
- Search coverage is web-surface only; a full formal/manuscript-stage novelty
  review (including the publisher PDF if later obtained) remains required.
