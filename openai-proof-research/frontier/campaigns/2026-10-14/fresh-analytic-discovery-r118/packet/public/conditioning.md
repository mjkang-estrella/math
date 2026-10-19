# Convex conditioning and logarithmic cost — prefreeze comparison

Let mu be a centered log-concave probability density with the linear subgaussian parameter a of source093, and let E be convex measurable with delta=mu(E)>0. These are exploratory hypotheses, not a frozen candidate. The source applies to the centered conditional law once its marginal scale is checked. The logarithmic loss has a classical complete compatible reduction.

Put L=log(2/delta)/log 2 >=1. For a unit theta and X distributed as mu(.|E), Holder/Jensen gives

    E exp(<X,theta>^2/(a^2 L))
       <= (E exp(<X,theta>^2/a^2))^(1/L)
       <= (2/delta)^(1/L)=2.

The first expectation inside the rightmost bound is under the conditional law; the original law supplies its upper bound 2/delta. If Y=<X,theta> and m=E Y, Jensen gives m^2<=a^2 L log2. Since (Y-m)^2<=2Y^2+2m^2, Cauchy--Schwarz gives

    E exp((Y-m)^2/(4a^2 L))
       <= exp(m^2/(2a^2L))
          (E exp(Y^2/(a^2L)))^(1/2) <=2.

Thus the conditional centered law has linear scale at most 2a sqrt L. It is log-concave and has a full-dimensional density because E has positive mu mass. Translation changes no gradient energy. Source093 `thm:main` therefore gives entropy coefficient at most 4C a^2 L. This uses every convex E and every delta>0 and has no dimension-dependent factor. It is a direct marginal calculation followed by the existing theorem, not a new compatibility mechanism.

The strongest inspected primary is Barthe--Milman [1202.5318v1](https://arxiv.org/pdf/1202.5318v1), Theorem2.4. With p=2, the density ratio 1_E/delta has L2(mu) norm delta^(-1/2). The target law has the paper's convexity assumption, including its total-variation approximation convention. Their kappa=0 conclusion gives the same O(1+log(1/delta)) loss from any supplied LSI. Proposition2.2 transfers concentration via density-ratio truncation; Theorem2.4 then uses concentration-to-isoperimetry and Gaussian isoperimetry-to-LSI. The proof passages of Proposition2.2/Theorem2.4 and the convexity definition were read; the cited deeper isoperimetric theorem was not freshly proved/read in its original source. The source093 calculus already includes convex approximation, anisotropic positive-curvature posteriors, tensorization and Gaussian-channel identities. No all-tilt transport map is supplied or claimed.

A simple sharp-order diagnostic explains why a loss-free conditional statement is not a promising candidate. On R2 take density Z^-1 exp(-max(x^2,y^2)). The potential is convex and even, and the measure has a fixed finite subgaussian parameter because max(x^2,y^2)>=(x^2+y^2)/2. Let E_R={y>=R}, R>=1. Conditional on y, the x density is constant e^-y^2 on [-y,y] and has Gaussian tails outside. Its denominator is

    2y exp(-y^2)+2 integral_y^infinity exp(-x^2) dx
       <= (2y+1/y) exp(-y^2).

Its x^2 numerator is at least (2/3)y^3 exp(-y^2). Therefore E[x^2|y]>=2y^2/9 for y>=1, and Var(x|E_R)>=2R^2/9 by x symmetry. Also integrating the marginal denominator gives

    Z^-1 exp(-R^2) <= mu(E_R)
       <= Z^-1(1+1/(2R^2)) exp(-R^2).

Consequently log(1/mu(E_R))=R^2+O(1). Linearization of an entropy inequality Ent(f^2)<=K integral|Df|^2 gives K>=2 Var(x), justified by truncation. The conditional coefficient must thus grow at least as a constant times log(1/delta). This elementary example is not a new nominee or a refutation of the logarithmic estimate. It also does not address every exponential-tilt or optimal-transport question.

All calculations preceded selection; no target was frozen, weakened, or submitted for independent gates. No primary novelty claim is made for the bound or example.
