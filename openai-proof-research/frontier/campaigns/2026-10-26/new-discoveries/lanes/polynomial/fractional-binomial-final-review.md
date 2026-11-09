# Final independent review — fractional-binomial converse, MathDB 352508

Date: 2026-10-26. **Mathematics PASS; exact source correspondence PASS; fresh full formal replay PASS (67 declarations in seven modules).** No missing Gamma, grid, finite-sum, anchor, homogeneity, or boundary bridge was found. The manuscript's stronger biased bound and coefficient optimality are also proved and formally certified. Under the documented-prior-art/no-known-prior-resolution standard, I recommend ACCEPT as one new-resolution candidate; this review does not change any tally. Novelty is assessed separately in `fractional-binomial-novelty-review.md` and is provisionally favorable with explicit literature-access limits, not an absolute priority guarantee.

No manuscript/proof/candidate/shared-index/git edits were made. Formal replay used independent copied files under `polynomial/review-fractional-binomial-final/`. Disclosure: I authored the supporting `GridRanks` module earlier; its reread here is not an independent authorship review of that one module. Parent review/integration supplies the additional review of that component. The Gamma/convexity/endpoint modules were authored by another worker.

## Exact reviewed bytes and replay

Reviewed manuscript `candidates/fractional-binomial/main.tex` SHA256:

`e9ab2cf89272e467a0822e9f5644a2ea24fc1336d1864f207a198d28b0e281c0`.

Frozen first six modules were copied from `lanes/matrix/fractional-binomial/formal/`; the parent-authored seventh module was copied from `candidates/fractional-binomial/formal/`. All seven candidate-integrated hashes were checked against the replayed bytes:

| Module | Declarations | SHA256 |
|---|---:|---|
| GridRanks | 20 | `96d0e22ac17128ffdd3287b8337b6b5cbcd9bdddd257b6dadbeac3378291757a` |
| GridMajorization | 3 | `f266df88f5648a1392930d8ec9f8da74a3345d8f8479f9db482d7b7163dfb78b` |
| GammaRatio | 14 | `21e8105a71b842d4769fe37d8b4f566049accb775f0e5af5728c13e6de0d5053` |
| ConvexExtrapolation | 3 | `1d8ecb8020010c69b27d4af51f6e13ea1e54d7369ae47519f1bc5c9172afe14d` |
| BinomialAnchors | 2 | `4c300a2cd16b8b5fdaea8d4cd8d748c82369f26a91cfe773e512272f9fa64863` |
| BinomialConverse | 19 | `ae48c6cebbc8a81362ca288ab66ccc0cca485e67cd785a9a872d4ba5fe0a44de` |
| BinomialRefinement | 6 | `37bf3cc6f353eda5f9b8b2b6a38ac284044ffc25f0601c1946aa30aaaedea5d1` |

Canonical `new-discoveries/verify_candidate.py` replayed all modules and every declaration with `warningAsError=true` against Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and checked the pinned package revisions. Independent audit:

`polynomial/review-fractional-binomial-final/build/verified/audit.json`

SHA256 `da79498f7f88145e6483392d04a1d9ea4c234930667955a511ecec2b9851d661`.

All 67 declarations passed, including `source_conjecture_352508`, `homogeneous_biased_bound`, and `sharp_coefficient`. Only `propext`, `Classical.choice`, and `Quot.sound` were observed. The source scan found no prohibited proof tokens. This is a complete endpoint audit, not merely a replay of a conditional extrapolation lemma.

## Formal statement and exact source fidelity

The final theorem is

    FractionalBinomial.source_conjecture_352508
      (k : ℕ) {a x y : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      (x+y)^(a*k) ≤ (2:ℝ)^(a-1) * binomialSum k a x y.

The sum is over `Finset.range (k+1)`. Its summand is the actual Gamma quotient

    Γ(a*k+1) / [Γ(a*j+1) Γ(a*(k-j)+1)] · x^(a*j)y^(a*(k-j)),

where `k-j` is natural subtraction and each use inside the finite sum has the proved bound j≤k. Thus it agrees with the generalized binomial coefficient used in Gerhold–Simon, [published Conjecture 3.2, printed p.634](https://link.springer.com/article/10.1007/s00605-022-01817-8), and [arXiv:2111.02747v2](https://arxiv.org/abs/2111.02747v2). The formal theorem includes the source's full real-parameter range a>2 and positive integers k, and additionally proves a=2 and k=0. Those extensions are boundary coverage, not separate discoveries. Real powers use the matching convention 0^0=1.

There is **no** `GridMajorizes`, Gamma convexity, positivity-of-inputs, log-convexity, or normalized-weight assumption on the final theorem. `gridMajorizes_proved` discharges the grid proposition by the concrete combinatorial theorem. The positive normalized theorem is combined with proved homogeneity and endpoint inequalities to obtain the full domain.

## Adversarial mathematical checks

**Rank maps and real grids.** The tie-breaking ranks L(r)=r+floor(lr/j) and R(s)=s+floor((js−1)/l) are strictly increasing, injective, and lie in the required finite interval. Both cross-collision cases in the manuscript are correct. The second uses js−1<js, which requires and has j,s>0. Cardinality plus disjoint inclusion gives exact coverage, including the final rank j+l. The multiplication comparisons have the right direction: jL≤(j+l)r and lR<(j+l)s. Consequently a decreasing function evaluated at the merged grid dominates the two separate-grid sums. No nonnegativity of the decreasing function is needed; the cardinalities agree. The formal comparison casts these natural inequalities using positive denominators and proves every grid point is in [0,1].

**Euler approximants and limit.** Grouping m=id+r, 1≤r≤d, in the finite Gamma product gives

    A_(d,N)(a)=da log(Nd)+log((Nd)!)-Nd log d
              −Σ_(i=0)^(N−1)Σ_(r=1)^d log(a+i+r/d).

The coefficient `−Nd log d`, all block limits, and r=1 rather than r=0 are correct. `gammaApprox_eq` identifies this with mathlib's logarithmic Gamma sequence at da plus log(da). The extra logarithm is essential: the sequence tends to log Γ(da), and Gamma's recurrence supplies log Γ(da+1). N↦Nd tends to infinity for d>0. All Gamma and logarithm arguments needed in the bridge are proved positive.

**Finite curvature and convex limit.** Twice differentiating gives a positive sum of inverse squares. Applying the grid theorem to t↦(a+i+t)^(−2) is legitimate for a>0 and i≥0, and yields curvature for A_(j+l,N)−A_(j,N)−A_(l,N) with the required sign. Convexity is passed through pointwise limits of finite convexity inequalities. The proof does not differentiate an infinite limit, assume uniform convergence, or postulate a trigamma formula. The zero cases j=0 or l=0 reduce to the constant function separately.

**Actual summand and finite log-sum closure.** `exp_logTerm_eq` proves the exponential of the convex log expression equals the exact Gamma/power summand on a>0,p,q>0. The finite log-sum theorem is fully proved using convexity of exp and positive normalized finite weights; it is not an assumed Hölder conclusion. Nonempty index range and strict positivity of the sums are supplied. Affine log p and log q terms do not change curvature.

**Anchors.** At a=1 the Gamma quotient is converted to `Nat.choose`, giving F(1)=(p+q)^k. At a=2 the separate even-binomial filter gives 2F(2)=(p+q)^(2k)+(q−p)^(2k). Its final term is nonnegative because 2k is an even integer. The natural subtraction in its powers is justified by j≤k; the extra terminal odd term has zero binomial coefficient. No assumption p=q occurs.

**Extrapolation and scale.** With t=1/(a−1), one has 2=(1−t)·1+t·a and 0<t≤1. Convexity therefore gives log F(a)≥(a−1)log F(2), not the opposite inequality. Combining F(2)≥1/2 and exponentiating yields the desired factor. Homogeneity is proved term by term using nonnegative bases, positive common scale, and a*j+a*(k−j)=a*k. The positive branch chooses scale x+y and the actual normalized weights.

**All zero cases.** The formal endpoint branches first on x=0 and then y=0. Proved nonnegative summands and the exact endpoint Gamma quotients give the necessary lower estimates; the factor 2^(a−1)≥1 completes these branches, including x=y=0 and k=0. The manuscript's stronger equalities at zero inputs and its k=0 discussion are mathematically correct. No log at zero or invalid division by x+y is used.

**Biased bound and optimality in the manuscript.** Retaining the exact F(2) gives

    S_k(a;x,y) ≥ (x+y)^(ak)[(1+(q−p)^(2k))/2]^(a−1).

The same argument works at a=2, and k=0 makes its factor exactly 1. With k=1,x=y>0 the main inequality is equality for every fixed a≥2, proving coefficient optimality. Both written arguments are correct and are now covered by the frozen seventh module. `convex_anchor_extrapolation` retains the exact log F(2), `normalized_biased_bound_positive` exponentiates it, and `normalized_biased_bound` proves the two normalized zero-input branches. `homogeneous_biased_bound` assumes exactly a≥2, x,y≥0 and x+y>0, matching the paper's biased formula. Its negative-division conversion gives q−p with the correct normalization. Finally, `binomialSum_degree_one` establishes S_1=x^a+y^a; `sharp_coefficient` tests any purported universal coefficient C at k=1,x=y=1 and derives 2^(a−1)≤C. It requires no prior nonnegativity of C. Combining this necessity theorem with `source_conjecture_352508` proves optimality, including a=2. No additional grid or convexity hypothesis is exposed by these refined endpoints.

## Citation metadata and manuscript status

The attribution of Gamma convexity as classical is correct. Alzer's exact scaled-probability theorem is recorded by [Qi–Guo §5.2, equation (5.1)](https://pmc.ncbi.nlm.nih.gov/articles/PMC7416756/); it should not be advertised as newly discovered here. [Hino–Namba v3](https://arxiv.org/html/2408.12011v3), revised 25 February 2026, and its published 2026 Theorem 2.9 retain the weaker Z≥a^(1−a²), with Z=aF. The manuscript compares the correct normalization and lower-bound direction.

The final manuscript metadata resolves the earlier cleanup points: Gerhold–Simon is identified as volume 200(3), pages 627–645; Hino–Namba as volume 395, article 9; and Qi–Guo as JMAA 493(1), article 124478, with its online-2020 date stated explicitly. Qi–Guo's issue date is 2021, as documented in the novelty review; the final citation's online date is accurate and the volume/article identify it unambiguously. No blocking citation error remains.

The final TeX was reread after the bibliography, coverage, and status changes. Its mathematical formulas and proof remain the reviewed argument. The abstract and final section now accurately state certificate coverage of the source inequality, biased refinement and optimality, with all 67 declarations and standard axioms. The source-access limitation is stated prominently: Alzer's entire article remained inaccessible, although its exact theorem and three corollary types were checked in accessible primary successors. This is a material novelty-search limit, not a formal or mathematical proof gap.

Under the agreed documented-prior-art/no-known-prior-resolution standard, my acceptance recommendation is favorable for **one** result. The known single-summand curvature is credited and no earlier full sharp bound was located; the simplicity of using classical ingredients does not itself establish prior publication. Absolute worldwide priority cannot be certified from this finite search. The separate novelty review supplies the search scope and evidence.

**Residual issues:** none blocking mathematical, source, formal, or textual acceptance of these exact bytes. PDF layout was not reviewed here; parent handles rendering and visual QA. Any later mathematical edit requires renewed review; metadata/status-only edits require a short text check and new hash binding. No external posting or count change is authorized by this report.
