# H009 prior-art review: raw Claude Opus report

Provider claudeAgent, model claude-opus-5-5; request
ecdloop-h009-crt-priorart-opus-20261008-r1. Completed, no experiment or repo edit.
Not adopted wholesale: quoted algorithm upper bounds are not lower bounds on all
implementations; support <=17^5 is not actual support =17^5. The exponent-scaling
claim needs actual surviving support and nonunit/coset accounting. The conditional
slice-density argument is unproved and unnecessary if the independently checked
two-variable first-quotient argument succeeds. No lower-arity pilot authorized.

# H009 prior-art and structural review: CRT encoding plus sparse leading-term Euclid

This review is read-only. I made no edits, ran no experiments or installs, launched no child agents and made no commits. I did extract PDF text into `/tmp/h009rev/` so I could read the papers.

**Verdict:**
- The CRT encoding is already published. The application to summation polynomials was not found in PKM or in one search.
- One known algorithm beats the literal recurrence, but it costs about q^(4/5) per query. That misses the q^(3/10) target, and it also misses √q per query.
- The one structural mechanism in BCR gives no gain on this family. No separate candidate version is warranted.
- **Verified improvement: NONE.** The square-root baseline is unchanged.

## Sources inspected

| Source | How I read it | Relevant content |
|---|---|---|
| Bi, Cheng, Rojas (BCR), [arXiv 1204.1113](https://arxiv.org/pdf/1204.1113); the SIAM version [10.1137/140990401](https://epubs.siam.org/doi/10.1137/140990401) returned 403 | Full text: Thm 1.1, Lemma 1.9, Thm 1.11, Prop 2.4, Lemma 3.1 | Algorithm and bounds below |
| Qiu, Cao, Huang, Feng, Gao, [arXiv 2606.12144](https://arxiv.org/pdf/2606.12144) (June 2026, preprint) | Abstract, related work, Lemmas 14–16 | Explicit CRT encoding |
| Petit–Kosters–Messeng (PKM), [PKC 2016](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf) | §§2.1, 3.2–3.4, conclusion | Single factor-base set V; Gröbner solving |
| Plaisted 1984 §3 and AIRR12 §§6.2–6.3 | Only as cited by BCR (Thm 1.11) and by Qiu et al.; not read directly | Origin of the encoding |
| Kelley [1602.00208](https://arxiv.org/pdf/1602.00208); Filaseta–Granville–Schinzel | Not inspected (FGS seen only through Qiu et al.'s summary) | Possible gap |

## 1. The encoding is prior art

Qiu et al. Lemma 15–16 use exactly H009's encoding:
- D = ∏ℓᵢ with D | p−1, ω a primitive D-th root of unity, and zᵢ = ω^(D/ℓᵢ).
- Polynomials are written in x^(D/ℓᵢ). Roots ω^m of x^D − 1 correspond through CRT to the residues (m mod ℓᵢ).

BCR Thm 1.11 builds the same structure over F_p with p = 1 + c·p₁⋯pₙ. It credits Plaisted 1984 §3 (complex roots of unity) and AIRR12. All three papers use the encoding only to prove hardness. I cite them for the encoding alone, not for any cost transfer.

PKM uses one subgroup or coset V for every variable. They impose membership through chained maps Lⱼ(x) = x^(pⱼ) and solve the system with Gröbner bases. Their cost formula is P + m!p/(deg L)^(m−1)·T + (deg L)^ω, and their stated open problem is a dedicated root-finding solver. They use no coprime per-coordinate domains, no single-variable packing and no gcd with x^N − 1. One web search found no paper combining summation polynomials with CRT gcd. So the application is apparently unpublished, but it only composes two known pieces.

## 2. Structural fact: the encoding is a relabelling

For t in μ_N, T^(N/Bᵢ) = ζᵢ ∈ μ_(Bᵢ). So f_R(t) = S6(u+ζ, x(R)) exactly. Write g(y) = S6(u+y, x(R)). Then gcd(T^N−1, f_R) is the eliminant, in the primitive element T = ∏zᵢ^(cᵢ), of the zero-dimensional ideal (zᵢ^(Bᵢ)−1, g). This is PKM's decomposition system with coprime cosets.

The encoding adds no information. It only fixes the representation, with:
- support t ≤ 17⁵ ≈ 1.42·10⁶; the exponents Σkᵢ·N/Bᵢ are distinct by CRT because kᵢ ≤ 16 < Bᵢ;
- degree D ≈ 16·Σ N/Bᵢ ≈ 80·q^(4/5).

## 3. Known operations that beat the literal recurrence, with bounds

**(a) BCR Prop 2.4: dense route.**
- Operation: compute T^N mod f_R by repeated squaring (O(log N) dense multiplications at degree D). Then run a Knuth–Schönhage half-gcd on (r−1, f_R).
- Cost: D^(1+o(1))·(log q)^(2+o(1)) bit operations, so K ≈ q^(4/5+o(1)).
- This fails K/σ < q^(3/10), and it exceeds √q per query. The relation phase alone, B·K/σ, is at least about q^(1+o(1)) for any σ = O(1).

**(b) BCR Lemma 3.1: roots of a t-sparse polynomial in an order-N subgroup.**
- Stated bound: 4^t·(t log N)^(O(1)) + N^((t−2)/(t−1)+o(1)), plus q^(1/4) to find a generator. At t ≈ 1.4·10⁶ this is useless.
- Their real mechanism scales exponents: x ↦ x^e, choosing e by a lattice shortest-vector search, which shrinks the degree, then enumerates δ' = gcd(e, N) cosets.
- Here the exponents live in the rank-5 span of Mⱼ = N/Bⱼ, and e·Mⱼ mod N = Mⱼ·(e mod Bⱼ). So the degree cannot drop below Mⱼ unless e ≡ 0 mod Bⱼ, which collapses that coordinate into Bⱼ coset branches.
- Collapsing any set J of coordinates costs B^|J| cosets × B^(4−|J|) degree = B⁴ in every case. **The mechanism is pinned at q^(4/5) on this family.** No separate candidate is merited.

**(c) Other routes are no better.**
- Enumerating x₁…x₄ and taking a degree-16 gcd in x₅ costs B⁴.
- Batching over targets, by taking the resultant in x(R) of the 17 coefficient polynomials, builds the full table, which costs at least N.

## 4. Cost of the literal recurrence

The number of leading-term steps in the first division of T^N − 1 by f_R equals |supp Q| exactly, where Q is the quotient.

- **Unconditional bound:** if f(0) ≠ 0, then |supp Q| ≥ (N−D)/D ≈ B/80. Any D consecutive zero coefficients would kill the order-D recurrence. This is about q^(1/5) and is **not decisive**.
- **Conditional bound:** assume S6 has the corner monomial ∏_(i≤5) xᵢ^16 with coefficient nonzero at x(R).
  - Let h(y) = y^κ·g(1/y), where κ = (16,…,16) is that corner exponent vector. Q's coefficients are the coefficients a_e of the power series 1/h(y), under the map e ↦ ⟨M,e⟩. This map is injective on ⟨M,e⟩ < N because eⱼ < Bⱼ. There are about N/120 candidate exponents.
  - Fix a slice e′ = (e₂,…,e₅) with |e′| = m. The y₁-series on that slice is P(y₁)/h₁(y₁)^(m+1), with denominator degree at most 16(m+1).
  - If a constant fraction of these slice series are not polynomials, then summing over m ≤ B/32 gives |supp Q| ≥ c·B⁴, with c roughly 1/(2·10⁷), i.e. Ω(q^(4/5)).
- The upper bound for the first division is about t·N. Every later Euclid step on a dense remainder costs up to D² ≈ q^(8/5).

## 5. Gaps

1. The corner coefficient of S6 has not been checked. If it fails, the argument has to use the tangent cone at a general vertex, where injectivity and cancellation are unproved.
2. Slice non-polynomiality is a genericity assumption.
3. I did not inspect Kelley or Filaseta–Granville–Schinzel. FGS applies only to inputs without cyclotomic factors, and T^N − 1 is cyclotomic, so it should not apply here.
4. Existence of the restricted prime family (five ~q^(1/5) coprime factors with N ≈ p dividing p−1) and the yield σ are still assumptions.
5. I found no sublinear-in-D method for gcd with x^N − 1 on this fixed-S6 family. Hardness results were not used for this conclusion.

## 6. Cheapest decisive falsifier

**Paper check (no experiment):**
1. Compute only the coefficient of ∏_(i≤5) xᵢ^16 in S6 as a polynomial in x₆. This needs leading forms through the resultant recursion, not all of S6.
2. Prove that slices are non-polynomial for a positive fraction of e′.

Together these show the literal recurrence needs Ω(q^(4/5)) steps per query. Combined with (a), every known operation sits at about q^(4/5) or worse, far above q^(3/10).

**Optional tiny diagnostic, if root authorizes one:** the same mechanism with the explicit S3, two coprime domains, and f = S3(u₁+T^(B₂), u₂+T^(B₁), x_R). Count |supp Q| against the predicted ~B₁B₂/2. Its cost is O(N·t) at toy sizes. It tests the genericity assumption only, not S6 constants.

Sources: [BCR arXiv](https://arxiv.org/pdf/1204.1113), [BCR SIAM](https://epubs.siam.org/doi/10.1137/140990401), [Qiu et al. 2026](https://arxiv.org/pdf/2606.12144), [PKM PKC 2016](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf), [Kelley](https://arxiv.org/pdf/1602.00208) (not inspected), [Davenport–Carette sparsity challenges](https://www.cecm.sfu.ca/~pborwein/MITACS/papers/DavCarette.pdf) (search result only)
