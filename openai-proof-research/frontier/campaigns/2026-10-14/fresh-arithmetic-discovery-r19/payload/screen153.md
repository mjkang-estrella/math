# Rational Bernoulli convolutions: full target unresolved

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0.

## Distinct target

For every rational λ∈(1/2,1), prove that the unbiased Bernoulli convolution ν_λ, the law of Σ_(n≥0) ε_n λ^n with independent fair signs, is absolutely continuous with respect to Lebesgue measure. No near-one restriction, bounded denominator, or density-regularity claim is substituted. This target was screened after182; it was not frozen or nominated. It is distinct from the earlier developed family153 Salem singularity extension in fresh-analytic-discovery-r11.

## Exact pinned interface

In family153 `Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026`, Theorem `cls:classification` defines R(n,d) as real units in (1/2,1) of degree dn whose minimal polynomial has coefficients −1,0,1 and irreducible reduction modulo2. Its sign is chosen with constant coefficient−1. W_n(r;d) is the set of distinct length-n coefficient prefixes of such polynomials with a root within4^−n of r. Closed orthants O_u are indexed by binary u; zero coordinates may belong to both sign choices. R_*(n,d,j) retains r if at least2^n/d orthants contain at least j(2r)^n prefixes. The source gives

    ν_λ singular ⇔ ∃d≥2 ∀j≥1 ∃ infinitely many n ∃r∈R_*(n,d,j): r−4^−n≤λ<r.

The same set results with 'all sufficiently large n' in place of 'infinitely many n'. The multiplier d is existential and unbounded, chosen before j. The criterion itself supplies no quantitative bound on crowding for rational λ.

The source's `cls:realization` is especially important: given a fixed λ, for every d above a λ-dependent d_0 and all sufficiently large n, every prefix satisfying its slab and first-coefficient hypotheses has an irreducible height-one degree-dn completion with root in (λ,λ+4^−n/2]. This is why simply excluding algebraic targets is not an available argument. The source's proof chooses D with λ^D<4^(−M), then d_0=2D+1, and can increase d without limit.

## Attempt1: rational separation does not control the quantifier d

Write λ=a/b in lowest terms, b>a≥1, b≥3. If f is one of the monic-up-to-sign degree-dn unit polynomials, the rational-root theorem gives f(a/b)≠0. Clearing denominators gives |f(a/b)|≥b^(−dn). On a fixed compact interval [u,v]⊂(0,1) containing λ and a nearby root r, coefficient boundedness gives |f'|≤(1−v)^−2, uniformly in its degree. Hence

    |r−λ| ≥ (1−v)² b^(−dn).

This lower bound is smaller than4^−n once d log b>log4 and n is large. Indeed b≥3,d≥2 already gives b^d>4. The existence of a positive separation bound is therefore not a contradiction to the required approximation. This establishes failure of this particular estimate, not the actual existence of retained roots for rational λ.

## Attempt2: the source's Garsia crowding argument has an exponential deficit

For distinct vectors w,w' in one orthant, their difference coefficients lie in{−1,0,1}. If P(t)=Σ_(i<n)(w_i−w_i')t^i were zero at a/b, removing an initial power of t would give a polynomial with leading and constant nonzero coefficients±1 having a nonintegral rational root, impossible. Therefore the prefix values are distinct and their spacing is at least b^(−(n−1)).

The source's `cls:slab` places all relevant prefixes in an interval of length2Bλ^n, with B depending only on λ. This separation thus gives at most

    1+2Bλ^n b^(n−1) = 1+(2B/b)a^n

prefixes in one orthant. The threshold is j(2r)^n, asymptotic to j(2a/b)^n for r−λ≤4^−n. The ratio of the two exponential rates is (b/2)^n, which grows. Consequently no fixed j can be chosen from this bound to exclude retention.

By comparison, the *actual pinned proof* `cls:garsia` uses algebraic norm2 and expanding conjugates to obtain spacing c_β2^−n. It then bounds an orthant by C_β(2λ)^n and takes j>C_β uniformly in d. This exact cancellation of2^−n with2^n is missing for rational λ. Replacing the expanding algebraic integer by a nonintegral rational reciprocal is not a valid norm2 argument.

## Primary operations and exact unpaid estimate

Varjú, arXiv:1602.00261v4, Theorem1, proves absolute continuity with LlogL density when λ is sufficiently close to1 in terms of its Mahler measure. Sections1.1–1.2 explicitly distinguish full dimension from absolute continuity: ordinary entropy convergence to the maximum gives dimension1, whereas the proof targets a summable deficit, e.g. H(μ;2^−n |2^(−n+1))≥1−C n^−2. Its Theorems2–3 improve entropy under convolution; selecting disjoint factors whose scale intervals overlap sufficiently uses the near-one hypothesis. No extension of that selection to all rational parameters has been supplied here.

Kittle–Kogler, arXiv:2409.18936v4, Theorem1.4 and Corollary1.15, improves the algebraic near-one sufficient condition to λ>1−C^−1 min{log M_λ,(loglog M_λ)^−2}. Its general hypothesis compares h/|χ| with C max{1,log(S/h)}². For λ=a/b, M_λ=b. This remains a sufficient near-one condition, not the unrestricted rational assertion. The exact primary statements were read; the entire proofs were not. An earlier author-site PDF search used different numbering; this report cites the downloaded v4 numbering.

To use the pinned criterion for the full rational target one must prove, for every rational λ and every d≥2, that there exists j≥1 such that all sufficiently large n admit no retained root r with r−4^−n≤λ<r. A direct sufficient estimate would control the fraction of orthants having more than j(2λ)^n relevant prefixes, uniformly as j grows, strongly enough to beat1/d. Alternatively, a summable entropy deficit or comparable uniform-integrability estimate would prove absolute continuity independently and then exclude the criterion. Neither rational separation nor injectivity of finite sums yields this. No new quantitative crowding or entropy estimate was proved, and no near-one corollary is counted.
