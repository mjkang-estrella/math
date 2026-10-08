# Raw H010 Opus prior-art review — claims require scoped disposition

Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h010-graeffe-priorart-opus-20261008-r1
Provider/model: claudeAgent/claude-opus-5-5. Status: completed.
Root does not adopt this report wholesale; see H010-graeffe-priorart-disposition.md.
The independent first-block obstruction was derived while this review was running.

# H010 review: prior art, applicability, and complete-cost threshold

**Verdict:** none of the cited bounds, and none of the prior art I checked, gives a per-query cost K/σ = o(B^{3/2}) for H010. Verified improvement: **NONE**. I edited nothing and ran no experiments. The only computation was one arithmetic line checking secp256k1's p−1.

The binding open question is still the support of intermediate polynomials. I did not find a rigorous cheap lower bound on that support. What I did find:
- A schedule-invariant formula for each block's output, given below. Any support bound has to hold for these outputs.
- A prior-art change to the threshold. Output-sensitive sparse multiplication relaxes the condition from 2ρ<3/2 to ρ<3/2. So a falsifier showing only S ≥ B^{3/4+ε} rules out the frozen literal schedule, not the idea.

## 1. What the cited papers assume (from the authors' PDFs)

**Grenet–van der Hoeven–Lecerf, deterministic paper (dmodroots).** I did not check the venue from the PDF.
- **Input:** a monic, separable polynomial f of degree d that splits over F_q ("irreducible factors have degree one and multiplicity one"). Algorithm 13 also needs f(0) ≠ 0.
- **Proposition 1 / Lemma 2:** requires χ = π₁⋯π_m to divide q−1, with primitive π_i-th roots given. Computing the Graeffe transforms costs O(m·M_q(μd)) or σ·Õ(d log q log μ), where μ = max π_i and σ = Σπ_i. Lemma 2 forms the dense product ∏ g(α^i x) in O(M_q(l·d)).
- **Proposition 14 (Algorithm 13):** write q−1 = ρπ₁⋯π_m. If d^{1+δ} ≤ q−1, the cost is σÕ(d log q) + (d log² q)^{1+δ} + Õ(d log³ q). This drops to Õ(d log³ q) when μ = max(ρ, π_i) = O(log q) and a primitive ρ-th root is given.
- **Descent:** step 3a builds the candidate list E from (e + jχ)/π_i. Step 3b prunes it by multipoint evaluation, and only when |E| > d.

**GvdHL, randomized tangent-Graeffe paper (rmodroots).** I did not check the venue from the PDF.
- **Setting:** an FFT field q = M·2^m + 1 with M = O(log q). The input is again monic, separable and split, with f(0) ≠ 0. The factorization of q−1 and a primitive element are treated as precomputed and their cost is excluded.
- **Proposition 9 (Algorithm 8):** a random additive shift f(x−τ) plus a tangent transform. Average cost Õ(d log² q) when d < q.
- **Lemma 7:** root recovery needs separable g and simple roots of the transform.
- **Proposition 12 (Algorithm 11):** conditional on a heuristic, or on f being a uniformly random split polynomial. Average cost Õ(d log² q).

**Why these bounds don't apply to H010:**
1. **The input does not split.** f_R is not split. Using these algorithms first requires gcd(f_R, T^N−1), which is the H009-type step. Neither paper pays for it.
2. **The cost scale is the degree.** Every bound is ≥ Ω(d), with dense arithmetic.
   - From per-variable degree 16 in S6, deg f_R ≤ 16·Σ N/B_i.
   - It is ≥ 16N/B₁ whenever the y₁¹⁶ coefficient survives specialization (I did not prove that it always does). Either way d = Θ(B⁴) = q^{0.8}.
   - The gate is q^{0.3}, so the cited bounds miss it by about q^{1/2} before any gcd cost.
3. **The randomization breaks the structure.** Algorithm 8's random additive shift τ moves roots out of μ_N, which destroys the cyclic structure H010 relies on. Proposition 12's "random split polynomial" distribution does not describe f_R.
4. **The descent itself is prior art.** H010's stored-layer descent is essentially GvdHL Algorithm 13 step 3, with explicit exponent bookkeeping. I checked the card's child map (k + t·n_{j+1}) myself: raising a child to the d_j-th power gives the parent, and distinct parents have disjoint children. Correct, but not novel.

## 2. A reformulation that places H010 in prior art (my derivation)

Write m_i = N/B_i and y_i = T^{m_i}. By CRT, f_R(T) = F(y₁,…,y₅) with F(y) = S6(u₁+y₁, …, u₅+y₅, x(R)).
- F has degree ≤ 16 in each variable, so supp F ≤ 17⁵.
- The exponents Σ e_i m_i are distinct mod N because each e_i ≤ 16 < B_i.

**Each step acts on one variable.** Take ζ of order 2 in the 2-block:
- ζ^{m₁} = −1, because m₁ is odd.
- ζ^{m_i} = 1 for i ≥ 2, because 2^{k₁} divides m_i.

So each Graeffe step in the 2-block touches y₁ only. The full 2-block computes G₁(y₂..y₅) = ∏_{y₁∈μ_{B₁}} F, reduced on a grid of size B⁴. Later blocks do the same for y₂, y₃, y₄, y₅. The final scalar is the norm of F over the whole grid, i.e. ±Res(T^N−1, f_R).

**This is PKM 2016 §3.3.** Their factor base is a subgroup of smooth order dividing p−1, with the map chain L_j(x) = x^{p_j}. Eliminating one level by resultant, Res_x(x^d − y, F(x)) = ±∏_t F(ζ^t·y^{1/d}), is exactly one Graeffe step. Their ledger gives the same gate: per-query cost must be below p^{1/2−1/m}, which is q^{0.3} = B^{3/2} for m = 5.
- **How H010 differs:** five coprime subgroups with additive shifts (so no m! factor), and Graeffe elimination instead of Gröbner bases.
- **PKM's own status:** practical only for small parameters, asymptotic complexity unknown. Their conclusion explicitly asks for a dedicated non-Gröbner algorithm for this "generalized root-finding problem". H010 is a candidate of that kind; PKM is not evidence that it is cheap.
- **Amadori–Pintore–Sala (FFA 2018):** the abstract claims a variant that beats Semaev's method and PKM in the prime-field case. I read the abstract only and accept no cost claim from it.

## 3. The complete-cost threshold

- **Expected decomposition count:** about N/q ≈ 1/c, where p = cN+1. So σ costs only a polylog factor, provided c = O(log p).
- **Query construction:** O(1) per query, if the setup charges a one-time expansion of S6(u+y, x₆). That expansion has at most 17⁶ ≈ 2.4·10⁷ coefficients. Asymptotically small, but a material constant.
- **Descent:** the expected number of grid zeros is O(1), so the V·S term is not the bottleneck.
- **Late stages are cheap.** Every n_j divides p−1, so a stage can run as a dense mixed-radix DFT in Õ(d_j·n_j). That fits the gate once n_j ≤ B^{3/2}, which happens partway through the 7-block (n_j runs from B² down to B there).
- **The binding stages are everything before that.** These are the stored outputs G₁ (grid B⁴), G₁₂ (grid B³) and G₁₂₃ (grid B²), plus all intermediate and partial products.
- **The bar depends on the multiplication method:**
  - Frozen pairwise schedule: need S ≤ B^{3/4−ε}.
  - Output-sensitive sparse multiplication (Giorgi–Grenet–Perret du Cray 2020; Arnold–Roche 2015): need S ≤ B^{3/2−ε}. That method is probabilistic, so its failures must be charged. It also needs characteristic larger than the degree, which can fail on the first step when N ≈ p−1; that step has only constant support, so naive pairwise multiplication covers it.
  - In particular, G₁₂₃ would need at most B^{3/2} terms out of B², and G₁ at most B^{3/2} out of B⁴.

None of these alternatives changes the full ECDLP cost unless such a support bound is proved.

## 4. The strongest cheap paper falsifier

**Target the schedule-invariant block outputs.** Write n = B₁ and let r_j be the y₁-roots of F, with leading coefficient a(y′). Using ∏_{ω∈μ_n}(ω − r) = ±(r^n − 1):

G₁ = ±a^n·∏_{j≤16}(r_j^n − 1) = ±Gr^{(n)}_{y₁}(F)(z=1), reduced mod (y_i^{B_i} − 1).

Here Gr^{(n)}_{y₁} is the order-n Graeffe transform in y₁. Its top coefficient is a^n and its constant term is ±F(0, y′)^n. Every intra-block ordering produces the same G₁, so every schedule has to pass through it.

**What a proof would decide:**
- Showing |supp G₁|, |supp G₁₂| or |supp G₁₂₃| ≥ B^{3/2+ε} for a positive fraction of targets falsifies both the frozen schedule and the output-sensitive variant.
- Showing only > B^{3/4+ε} falsifies just the frozen schedule.
- I expect these outputs to be dense, because a^n wraps about 16 times around the cyclic grid. That is a heuristic, not a proof: products and powers can cancel.

**A tempting argument that fails.** A nonzero S-term cyclic polynomial cannot vanish on S consecutive powers of a generator (Vandermonde). That gives (number of nonzero grid values)·S ≥ n. The block norms vanish at only O(1) points, so this bound is vacuous. A real proof has to use the product structure.

**If no paper proof turns up,** the cheapest decisive check is an exact support count of G₁ and G₁₂ at a few small balanced parameter sets. That is an experiment for root to authorize, and finite sizes cannot prove an exponent.

## 5. The restricted prime family

- **The shape is very narrow.** N ≈ q with all prime factors in {2,3,5,7,11} means p−1 is essentially 11-smooth, with each B_i within a factor ℓ_i of q^{1/5}. Only polylog-many balanced N exist per bit length.
- **Existence is heuristic.** p = cN+1 being prime for some c = O(log p) is a Dickson/Bateman–Horn-type heuristic, not proved. Insisting on p = N+1 leaves O(1) candidates per size, which will often contain no prime.
- **Prime order is also heuristic.** A curve of prime order over such a p is expected by the usual heuristics, also unproved.
- **No secp256k1 transfer.** The {2,3,5,7,11}-smooth part of secp256k1's p−1 is exactly 42 (my one arithmetic check), against the ≈2²⁵⁶ needed.
- **For contrast:** GvdHL's FFT primes (M·2^m+1) and PKM's §3.3 have the same kind of special-structure requirement. PKM notes that NIST P-224's p−1 qualifies for their attack.

I agree with the card that the H009 reciprocal-series proof does not carry over to this cyclic norm.

Sources:
- [GvdHL, deterministic Graeffe root finding](https://www.texmacs.org/joris/dmodroots/dmodroots-abs.html) ([PDF](https://www.texmacs.org/joris/dmodroots/dmodroots.pdf))
- [GvdHL, tangent Graeffe](https://www.texmacs.org/joris/rmodroots/rmodroots.html) ([PDF](https://www.texmacs.org/joris/rmodroots/rmodroots.pdf))
- [Petit–Kosters–Messeng, PKC 2016](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf)
- [Amadori–Pintore–Sala, ePrint 2017/609](https://eprint.iacr.org/2017/609) (abstract only)
- [Giorgi–Grenet–Perret du Cray, ISSAC 2020](https://arxiv.org/abs/2001.11959)
- [Arnold–Roche, ISSAC 2015](https://arxiv.org/pdf/1501.05296)
