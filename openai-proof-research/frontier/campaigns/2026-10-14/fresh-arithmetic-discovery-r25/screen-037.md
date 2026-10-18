# Family037: next-gap screen, no nominee

This is an author-side pre-freeze screen. Count remains13/20. No full research target was frozen, and no sharp arbitrary-klt second-gap theorem is asserted. The stipulated source is the pinned all-dimensional ODP manuscript and its fourfold companion. The source's truth is accepted throughout.

## Exact source and the proposed operation

The all-dimensional introduction, `thm:main`, treats every singular closed point of a normal complex algebraic n-fold, n≥2, with Q-Cartier canonical class and klt singularities near that point, with zero boundary. It gives normalized volume at most V_n=2(n−1)^n, with equality exactly at an analytic ordinary double point. Isolatedness, hypersurface structure and smoothability are not hypotheses. The fourfold companion's `thm:main` supplies the same unrestricted statement for n=4, V_4=162. Its stronger intermediate structural implication has the hypothesis volume≥162 and gives embedding dimension≤5.

The provisional question was whether strictness in the source could give, for each fixed n, ε_n>0 such that every singular non-ODP germ in that same unrestricted class has volume≤V_n−ε_n. It was screened before freezing or claiming a new mechanism.

## Primary comparison: the existential question is already paid

Xu–Zhuang, *Boundedness of log Fano cone singularities and discreteness of local volumes*, [arXiv2404.17134v2](https://arxiv.org/html/2404.17134v2), Theorem1.2, makes zero the only accumulation point of local volumes in fixed dimension and with a fixed finite coefficient set. Take coefficients {0}. Its proof uses volume-preserving stable degeneration, boundedness and constructibility. Theorem1.1 and the complete Theorem1.2 proof were inspected; the proof of boundedness was not independently read.

Indeed, if the proposed ε_n did not exist, choose non-ODP singular germs with volumes in (V_n−1/j,V_n). The strict upper endpoint follows from the stipulated equality characterization. Their volumes approach the positive number V_n, and a subsequence has distinct values. This contradicts discreteness away from zero. Thus the entire existential assertion is a direct combination of a primary theorem and the pinned equality characterization. It is not a substantial new deduction for this campaign.

## What an explicit bound would need beyond the equality proof

Write N=n−1 and p_n=V_n/n^n. Source `boot:holder` bounds a cone's density by p_n/2+d(Y)/h, where Y is a singular klt slice of the same dimension and h≥2. After the ODP theorem, this is at most p_n. It does not decrease the endpoint when h=2 and d(Y) is close to p_n. In particular the source does not show that excluding an ODP input excludes an ODP slice.

At exact equality `boot:equality-data` forces h=2, A'=Nℓ, and, after ℓ=1, σ=2 and w=(2N/n)wt_ξ. This last identification uses uniqueness of the minimizing valuation: w must itself attain the minimum. A near-extremal w need not be identified by uniqueness alone. A quantitative stability statement for the minimizing valuation is an additional obligation.

Source `boot:strict-count` proves that w(v)>2 would lose a positive leading colength. For any 1/w(v)<t<1/2 its loss is (1/2−t)^n. Such losses tend to zero as w(v) decreases to2. The eventual rounding `boot:rounding` uses fixed-cone eigen-generators and w(v)=2Nm/r+o(1/r), hence an integer Nm−r≤o(1). It assumes the exact equality identification of w. It supplies neither a uniform quantitative comparison for near-minimizers nor a bound on the approximating grading denominator r across all cones. No contradiction in the source is asserted.

There is an earlier hypothesis to check as well: `jet:moments` derives H≥2/s directly from volume≥2N^n. Below this threshold it gives only H≥volume/(N^n s). The exponential-envelope theorem has the absolute constant C_*=(3/4)e^(4/3)−e/3<2; any proposed lower threshold must still dominate the appropriate envelope after the other moment errors. Merely retaining the printed conclusion with 2 replaced by a smaller number is not justified. Even if this interiority step survives a chosen threshold, it does not repair the h=2 and near-minimizer obligations above.

## A complete elementary support calculation, explicitly not a substitute

For a singular klt hypersurface germ that is not ODP, the source's weighted hypersurface test already gives the explicit upper bound

    H_2=4/3, H_3=125/9,
    H_n=2 n^n ((n−2)/(n−1))^(n−1) for n≥4.

Here is the deduction. Let q be the multiplicity. The equal-weight test gives q(n+1−q)^n, and klt implies 2≤q<n+1. This expression decreases with real q>1. Thus q≥3 gives at most3(n−2)^n. For n=3 this is3<125/9; for n≥4 its ratio to H_n is

    (3/2)(1−2/n)(1−1/n)^(n−1)<1.

For example, (1−1/n)^(n−1)≤1/2 follows from Bernoulli's inequality (1+1/(n−1))^(n−1)≥2, so the ratio is at most3/4. For n=2, q≥3 is excluded by q<n+1.

If q=2 and the quadratic form is nondegenerate, the analytic Morse lemma makes the germ ODP, excluded here. Otherwise choose one coordinate absent from the quadratic form. Assign it weight1−ε and give all other coordinates weight1. For 0<ε≤1/3, the weighted order of the equation is2: a nonzero quadratic term has that weight, and every higher ordinary-degree term has weight≥3(1−ε)≥2. The source's test permits this endpoint and does not require the initial equation to be reduced. It yields

    volume≤2(n−1−ε)^n/(1−ε).

Take ε=1/3 for n=2,3, and ε=1/(n−1) for n≥4. These are exactly H_n. Also H_n<V_n: for n≥4 the logarithmic derivative of this displayed expression is negative for 0<ε<1/(n−1), and its endpoint remains strictly below its value at zero; the cases n=2,3 are immediate. This is a short explicit version of the source's own hypersurface strictness calculation. It is not a new arbitrary-klt result, not a claimed sharpness theorem, and not nominated. No assertion that all germs in the volume interval (H_n,V_n) are hypersurfaces has been proved here.

## Disposition

The existential full-scope question is technical. A sharp explicit unrestricted next gap would need genuinely new structural information, not a restriction to hypersurfaces or a parameter version of the equality proof. This screen provides no credible complete bridge to that stronger task, and none was frozen. The finite calculations accompanying this note check formulas only.
