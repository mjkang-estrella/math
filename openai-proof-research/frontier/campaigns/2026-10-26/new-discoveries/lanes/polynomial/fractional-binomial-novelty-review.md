# Independent novelty review of the full sharp fractional-binomial converse

Date: 2026-10-26. Target: MathDB 352508, Gerhold–Simon Conjecture 3.2. This review concerns publication history and attribution of the **full finite-sum bound**, not its formal replay. No discovery tally, other artifact, or git state was changed.

**Result: provisionally favorable novelty screen for the full conjecture resolution.** The retrieved primary sources establish the classical single-summand convexity and stronger monotonicity properties, but none was found explicitly stating or proving the sharp full converse for every real α>2. The source published in 2023 labels exactly that bound a conjecture. The latest relevant 2026 primary treatment still states a substantially weaker uniform lower bound. A short deduction from classical ingredients can resolve an explicitly open conjecture; proof simplicity is not evidence of earlier publication. Absolute novelty remains unproved, with the specific retrieval limitations below.

## Exact claim under review

Write

    F_α(k,p) = Σ_{j=0}^k Γ(αk+1)/[Γ(αj+1)Γ(α(k−j)+1)]
                         ·p^(αj)(1−p)^(α(k−j)).

The target is F_α(k,p)≥2^(1−α) for real α>2, positive integer k, and 0≤p≤1. This is precisely the homogeneous x,y≥0 statement in Conjecture 3.2 after normalizing x+y=1. The coefficient is sharp already for k=1,p=1/2; the original conjecture identifies its sharpness, so that observation carries no separate novelty claim.

Primary original: Stefan Gerhold and Thomas Simon, *A converse to the neo-classical inequality with an application to the Mittag-Leffler function*, [published 2023 version](https://link.springer.com/article/10.1007/s00605-022-01817-8), printed p.634; [arXiv:2111.02747v2](https://arxiv.org/abs/2111.02747v2), revised 15 December 2021. Both explicitly retain Conjecture 3.2. The title's proved “converse” refers to other parameter ranges, not a proof of this conjecture.

## What Alzer and the gamma-ratio literature actually establish

Horst Alzer, *Complete monotonicity of a function related to the binomial probability*, J. Math. Anal. Appl. 459(1) (2018), 10–15, DOI [10.1016/j.jmaa.2017.10.077](https://doi.org/10.1016/j.jmaa.2017.10.077), establishes complete monotonicity on t>0 of

    G(t)=Γ(nt+1)/[Γ(jt+1)Γ((n−j)t+1)] ·p^(jt)(1−p)^((n−j)t)

for integer 0≤j≤n and 0<p<1. This is the **exact summand**, not merely an analogous function. Its logarithmic complete monotonicity, hence log-convexity, is also recorded in the later primary literature. No novelty should be claimed for the summand's convexity.

Access qualification: the publisher landing page and the OpenAlex-listed official PDF URL returned HTTP 403 in this review; no complete Alzer PDF was obtained. The exact theorem was checked through two independent accessible primary reproductions, not inferred from a search snippet:

- Feng Qi and Bai-Ni Guo, *From inequalities involving exponential functions and sums to logarithmically complete monotonicity of ratios of gamma functions*, DOI [10.1016/j.jmaa.2020.124478](https://pmc.ncbi.nlm.nih.gov/articles/PMC7416756/), published online 2020, issue 2021. Section 5.2, equation (5.1), gives the exact function and explicitly attributes complete monotonicity to Alzer, including the logarithmic strengthening. Later sections study gamma ratios and trigamma combinations; they do not give the target finite-sum converse.
- Frédéric Ouimet, *Complete monotonicity of multinomial probabilities and its application to Bernstein estimators on the simplex*, [arXiv:1804.02108v2](https://arxiv.org/html/1804.02108v2), JMAA 466(2) (2018), 1609–1617, DOI 10.1016/j.jmaa.2018.06.049. Theorem 2.1 generalizes Alzer to multinomial rays. Section 3, Corollary 3.1, explicitly generalizes Alzer's three coefficient inequalities: log-convex interpolation, a product-versus-sum inequality in the scaling parameters, and a two-factor rearrangement inequality. These are not the finite sum over j in the target.

Finite sums of positive log-convex functions are log-convex, so the needed log-convexity of F_α is already a classical consequence of these results. The full sharp bound nevertheless requires applying that fact to the exact anchors F_1=1 and F_2=[1+(1−2p)^(2k)]/2≥1/2, then extrapolating to α>2. I found no statement of that application or the resulting sharp bound in the inspected papers. The proposed proof's publication-level contribution is this full conjecture resolution, not a new theorem on gamma curvature.

## What MathOverflow 280075 establishes

The [original 2017 discussion](https://mathoverflow.net/questions/280075/proof-of-complete-monotonicity-of-a-binomial-function) studies one function f(t)=log binom(t,pt). Its initial decreasing/complete-monotonicity suggestion is corrected in the answers: f′ is positive, while f″ is completely monotone. Suvrit's answer uses Karp–Prilepkina's gamma-ratio criterion; David Speyer and other contributors establish the necessary positive exponential kernel. A later answer collects Alzer, Ouimet, Qi, and related extensions. There is no finite sum over the binomial index, no anchors at scaling parameters 1 and 2, and no stated sharp converse for α>2.

The appropriate credit includes the known gamma-ratio curvature argument and its exponential-kernel proof. Citing the initial erroneous monotonicity suggestion as a theorem would be inaccurate. The discussion is primary evidence for the posted arguments, not a source claiming the target conjecture was resolved.

## Strongest relevant bounds located in the original and newer sources

All entries below use the normalized F_α above. Hino–Namba instead use Z_(α,p)^(k)=αF_α; forgetting this factor would give the wrong comparison.

| Scope | Retrieved proved bound | Primary location |
|---|---|---|
| 0<α<1 | F_α≥1; also αF_α≤1 | Gerhold–Simon Theorems 1.2–1.3, with the neo-classical upper estimate credited to Hara–Hino |
| α>1 | F_α≤1 | Gerhold–Simon Theorem 1.3 |
| 1<α≤2 | F_α≥1/α | Hara–Hino consequence stated immediately before Gerhold–Simon Conjecture 3.2 |
| all α≥2, uniformly in k,p | F_α≥α^(−α²) | Hino–Namba Theorem 2.9(2), equivalently Z≥α^(1−α²) |
| fixed interior p and fixed α, k→∞ | F_α→1/α, with exponential error in the stated compact parameter regimes | Hino–Namba normalization asymptotics; asymptotic, not a sharp finite-k uniform lower bound |
| target, all real α>2 and all k,p | F_α≥2^(1−α) | Still conjectured in Gerhold–Simon; no earlier proof located |

I checked the actual latest [arXiv:2408.12011v3](https://arxiv.org/html/2408.12011v3), revised 25 February 2026, not just the older v2. Theorem 2.9 still gives the weaker bound in the table. Its [published version](https://link.springer.com/article/10.1007/s00208-026-03424-6) is Masanori Hino and Ryuya Namba, Math. Annalen 395, article 9 (2026). For α≥2, α^(−α²)<2^(1−α), since α² log α>(α−1)log 2. The asymptotic limit also does not settle a uniform inequality over all finite k and p.

The related [Hino–Namba asymptotic paper, arXiv:2506.10438v1](https://arxiv.org/abs/2506.10438), concerns large/moderate deviations and a Berry–Esseen estimate. It was not found to supply the sharp converse.

A further title search found Elina Shishkina, Sergei Sitnik and Viktor Polunin, *On sharp bounds in the T. Lyons's neo-classical inequality*, Global and Stochastic Analysis 8(2) (2021), 77–86. Its [actual publisher PDF](https://www.mukpublications.com/resources/gsa%20v8-2-8_SitShishStoh.pdf) studies an upper bound with reciprocal parameter p≥1, corresponding to α≤1. It therefore does not cover the present α>2 lower bound. Its concluding discussion also leaves the opposite-sign lower-bound problem for future work. The similar title is not evidence of a prior resolution here.

## Additional checks and candid conclusion

Searches covered the exact original title, identifier, conjecture number with author names, sharp/complete-monotonicity/convexity variants, and fractional-binomial lower bounds. The original author's current publication list and September 2025 addenda do not report a resolution. A small OpenAlex forward-citation check identified four indexed citing works; their relevant topics/text were checked, including the 2025 Garrappa–Gerhold–Popolizio–Simon paper [arXiv:2410.11852v4](https://arxiv.org/html/2410.11852v4), the Ferreira–Simon Wright-function paper [arXiv:2212.07974v2](https://arxiv.org/html/2212.07974v2), and the [2022 fractional-characteristic-function paper](https://link.springer.com/article/10.1007/s13540-022-00047-x). No full-bound resolution was found there. Citation indexes and search engines have incomplete coverage.

My assessment is therefore: **the inspected literature supplies the classical ingredient, but does not explicitly establish the full sharp endpoint.** The continued weaker bound in a 2026 primary treatment supports the interpretation that this is a real, previously unresolved finite-sum question, while not proving that no unpublished, unindexed, or inaccessible resolution exists. I would retain the valid full proof as a candidate new resolution, with narrow and explicit attribution, rather than reject it solely because the argument is short. This is not certification of priority, and this report changes no count.

The earlier mathematical review's warning about “classical-consequence” simplicity should be understood as an attribution warning, **not as evidence of an earlier published proof of the full conjecture**. A valid final paper can accurately say it proves Gerhold–Simon Conjecture 3.2 by a short application of classical log-convexity, and credit Alzer, Karp–Prilepkina, Ouimet, Qi–Guo and the relevant posted curvature arguments. It should avoid claiming those classical facts as discoveries or describing the conjecture's sharp coefficient as newly guessed.

Remaining novelty limit: direct inspection of Alzer's entire six-page article was blocked, even though the exact theorem and the character of its three corollaries are reproduced by accessible primary successors. There was no author contact, external posting, or attempt to bypass access restrictions.
