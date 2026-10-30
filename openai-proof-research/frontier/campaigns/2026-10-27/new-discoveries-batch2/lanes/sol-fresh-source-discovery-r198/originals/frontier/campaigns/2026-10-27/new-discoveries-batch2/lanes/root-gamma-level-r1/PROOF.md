# Provisional full gamma-level convexity theorem

Root ordinary proof candidate; no count. Independent proof/source/prior-art/substantive review and full Lean absent. This is a distinct implicit gamma-ratio curve, not the previously accepted Simon threshold function. Scope/family eligibility is not assumed from that distinction.

Exact source: Garrappa-Gerhold-Popolizio-Simon arXiv2410.11852v4 (11 May 2025), Lemma15 and Remark16(a), PDF pages9-10. Local v4 PDF SHA256 b40a207a03980285ad9d821b6201da7eacabd5d0c0b4b5faea6b6f2ed0d48874. Root visually read the complete page10 including Remark16(a). For x>0 the source defines h(x)>0 by

    Gamma(h) Gamma(h+2x) / Gamma(h+x)^2 = 2.

It proves existence, uniqueness, analyticity, monotonicity and strict convexity on[1,infinity), then explicitly believes strict convexity on the whole(0,infinity). The latest v4 additionally uses h in Theorem23's positive-half-line ML log-convexity/log-concavity classification, including alpha<=1. The older v2 remark about relevance only for alpha>=2 must not be used to characterize v4. The source's separate main Conjecture26 (the older version's MathDB365327 question) is NOT resolved by the argument below. Its 'log E' is explicitly up to translation in the surrounding text; a missing additive normalization is NOT a refutation and receives no credit. Journal citation: JMAA551(1)(2025)129588, DOI10.1016/j.jmaa.2025.129588. The actual journal PDF remains locally inaccessible (official repository requests return403); indexed text is supporting evidence, not a visual journal-body comparison.

## Stronger one-family theorem to investigate

For any fixed c>1 and x>0 there is a unique h_c(x)>0 with

    Gamma(h_c(x)) Gamma(h_c(x)+2x) / Gamma(h_c(x)+x)^2 = c.

The function h_c is strictly convex on(0,infinity). For c=2 this would resolve the exact source Remark16(a). All c instances would be ONE family, never separate outcomes. Newness/substance unverified.

## Complete ordinary proof route

Let s=x+y, and define for 0<x<s

    F(x,s)=log Gamma(s-x)+log Gamma(s+x)-2log Gamma(s).

Euler's gamma product, with the linear/exponential factors cancelled, gives

    F(x,s) = sum_(m>=0) -log(1-x^2/(s+m)^2).

The series converges absolutely and locally uniformly on0<x<s because its terms are O(m^-2), uniformly on each compact subset. Equivalently, with

    g(u)=-log(1-u^-2)=log(u^2/(u^2-1)), u>1,

we have F(x,s)=sum_m g((s+m)/x). Direct differentiation gives

    g'(u)=-2/(u(u^2-1)),
    g''(u)=2(3u^2-1)/(u^2(u^2-1)^2)>0.

Thus g is strictly convex and decreasing on(1,infinity).

For each s>0, F(x,s) is continuous and strictly increasing in x from0 toinfinity as x increases from0 tos (the m0 term diverges). Hence there is a unique rho(s) in(0,s) satisfying F(rho(s),s)=log c. For fixed x, F(x,s) strictly decreases with s, so rho is strictly increasing. Moreover rho(s)->0 as s->0 (since rho(s)<s), and rho(s)->infinity as s->infinity: for every fixed M>0, F(M,s)->0 by comparison with C M^2 sum_m(s+m)^-2 ->0. Consequently rho is a continuous increasing bijection of(0,infinity), with continuous inverse s_c(x). Existence/uniqueness of h_c=s_c(x)-x>0 follows, including all x>0.

We prove rho is strictly concave. Take s0!=s1, lambda in(0,1), x0=rho(s0), x1=rho(s1), S=lambda s0+(1-lambda)s1, X=lambda x0+(1-lambda)x1, and a=lambda x0/X in(0,1). For every integer m>=0,

    (S+m)/X = a (s0+m)/x0 + (1-a) (s1+m)/x1.

Jensen's inequality for g therefore yields

    g((S+m)/X) <= a g((s0+m)/x0)+(1-a)g((s1+m)/x1).

At least one of m=0,1 gives a strict inequality: if both ratios on the right were equal, subtraction would give1/x0=1/x1, then s0=s1, contradiction. Summing the absolutely convergent inequalities, with that strictly positive one-term gap, gives

    F(X,S) < a log c+(1-a)log c = log c.

By strict increase in the first argument, X<rho(S). This is strict concavity of rho. The inverse of a strictly increasing strictly concave function is strictly convex: apply the preceding strict inequality to s_i=s_c(x_i) and then the increasing inverse, to obtain

    s_c(lambda x0+(1-lambda)x1)
      < lambda s_c(x0)+(1-lambda)s_c(x1).

Subtracting the affine function x proves strict convexity of h_c on the entire positive half-line. No derivative of the implicit curve is needed. All convergence and uniqueness facts have been included above; the only classical dependencies are Euler's gamma product and Jensen convexity.

## Strongest objections and remaining gates

1. This may be a routine corollary of a known harmonic-Orlicz mean concavity or gamma-ratio level-set theorem. Exact prior-art investigation and independent substantive judgment are mandatory before any large Lean effort or credit.
2. The source already proves convexity for x>=1, so the new c2 content is the entire interval(0,1); v4's Theorem23 does use h for small positive alpha. Under the user's strict rule this could still be judged an uncountable parameter-range extension rather than a substantive new outcome. The general all-c theorem is not automatically new or separately countable.
3. Latest arXiv/publication/source-body and possible followups must be compared. No claim that this is unresolved in the current literature is made yet.
4. A complete Lean endpoint would require a genuine logGamma/product/series bridge, strict Jensen summation and inverse-curve argument, not merely an abstract convexity theorem with those facts assumed.
5. This does not resolve v4 ML Conjectures25/26, the non-real-zero boundary f, or any source complete-Bernstein classification. No numerical evidence is used as the proof.

## Root checks and first prior-art screen

The own symbolic derivative check simplifies the displayed g'' identity to zero. Twenty-five 70-digit numerical bisection probes of rho give positive strict-concavity margins for levels c=1.01,1.2,2,5,100 and pairs of s covering 0.0001 to200. These are diagnostics, not interval certificates and not a proof; see checks.json.

Read the main theorem bodies of Himmel-Matkowski, Directional Convexity and Characterizations of Beta and Gamma Functions, JCA25(2018)927-938, DOI10.68381/jca25060 (official full PDF https://journalofconvexanalysis.com/articles/jca25060/jca25060.pdf?v=2). Theorem3.1 and Theorem3.5 characterize B(x,x+k) by a recurrence with directional log/geometric convexity. Section5 discusses ordinary directional Hessian criteria. No gamma-ratio implicit-level theorem is stated in those inspected bodies; this limited comparison is not a novelty clearance. General harmonic-Orlicz/perspective sublevel-set results remain a serious possible routine-subsumption mechanism. Multi-angle searches have produced mostly unrelated level-set and Orlicz-space results. No inference of novelty is made from search failure.

Pinned Mathlib has Real.BohrMollerup.tendsto_log_gamma and the explicit logGammaSeq definition. Thus a genuine finite-partial-sum-to-logGamma bridge appears feasible without a new special-function axiom. This is only an implementation observation: no Lean theorem for this candidate has been written or checked.
