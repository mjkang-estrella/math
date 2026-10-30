# Structural203 independent correctness review, round 1

**Full-scope verdict: PASS.** The submitted proof establishes the entire unchanged frozen Theorem A and Corollary B, at every displayed quantifier and constant, under the stipulated truth of Source327 and its operative upstream proofs. No essential objection, missing bridge, or necessary repair remains. The expansions below justify compressed steps of the submitted argument; they do not replace its construction, alter its constants, or freeze a different statement. This is a correctness verdict only. It assigns no contribution grade, acceptance, or count.

The reviewed author root is `frontier/campaigns/2026-10-14/fresh-structural-discovery-r203/`. Its `packet/FROZEN.md` is 3,579 bytes, SHA256 `850bd50cd2888d4f184e8b164f1e8dfbd2258181f65adf22dc4b21d71ea52576`, frozen at 2026-10-23T21:15:32.099049+00:00. Its submitted `packet/DERIVATION.md` is 19,479 bytes, SHA256 `64383e9146d43df52931ad2982b49bd1887660298803081835dde44d79d18f67`. Exact private copies are [the frozen statement](private/author-FROZEN.md) and [the submitted proof](private/author-DERIVATION.md). These copies preserve the author bytes, not a revised theorem. All references to author proof sections and equations below refer to these exact bytes.

The canonical source is `preprints/Nontrivial-Markov-Type-Forces-Superreflexivity-September-23-2026/` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Source line references refer to its 42,458-byte `build/main.tex`; all 1,020 lines, its figure include, references, README, and the indicated formal files were actually read. The source's chart/action constructions are paid premises where their hypotheses hold. In particular, the exact-spreading norm proposition is not a theorem about the finite approximate seminorm constructed here. Its scalar identities and norm-independent chart mechanism are used separately, followed by the author's robustness argument.

## 1. Fixed scope and parameter dependencies

Write `p>1`, integer `n≥1`, and `0<θ≤1`. The frozen definitions are

    L=8(n+1),
    m=8L+(L+4n+1) Σ_{j=0}^n 4^j,
    r₀=4^m,  c₀=(40nr₀+2)^(r₀),
    B=S(m,m,c₀),  A=B^m,
    C(n)=A(8nA²+1)^(2A²),
    σ=θ/(4L),  ξ=θ/(4096BL),  η=(ξ/24)²,
    Q=ceil(16/ξ),  T=ceil((16/ξ)^p),  H=BQ^T,
    J=ceil(4H/η),
    c₁=(ceil(2H/η)+2)^((2J+1)^H),
    M(p,n,θ)=S(H,H,c₁).

Here `R₁(s,c)=c(s−1)+1`; for `k≥2`, put `t=R_{k−1}(s,c)+1` and `R_k(s,c)=(t+1)c^(t^k)`. For `h≥a≥1`, `b_a=h`, `b_{k−1}=R_k(b_k,c)` for descending `k`, and `S(a,h,c)=b₀`.

Every recursive call decreases its arity and retains an integer second argument at least that arity. Inductively `R_k(s,c)≥s`, so `b_k≥h≥a≥k`. All numbers are finite, positive integers where integers are required. In particular `L≥16`, `B≥m≥8L`, `B≥3`, `2L≤B`, `L+2≤B`, `0<ξ≤1`, `0<η≤ξ`, and `Q,T≥1`. No enormous integer needs to be evaluated. The order of dependencies has no cycle: the chart parameters `L,m,r₀,c₀,B,A,C` depend only on `n`; all later norm-approximation parameters may depend on `p,n,θ`.

Theorem A assumes only the displayed approximate triangular array of length M in the original norm of an arbitrary real normed space. Its required output is one finite stationary reversible state chain of at most C(n) states, and one map into the real span of the supplied vectors, with one-step p-cost exactly 1 and n-step p-cost at least `(3/40)(n/96)^p`. No uniform stationary law, irreducibility, degree restriction, lower bound on positive stationary masses, completeness, separability, or dimension hypothesis is inserted below.

## 2. Ramsey recurrence and simultaneous thinning

Author §1 is valid, including its reservoir estimate. For k=1 pigeonhole gives exactly `c(s−1)+1`. For k≥2 maintain an ordered list of selected vertices and a common future reservoir. When selecting `v_i`, for each `(k−2)`-subset of preceding vertices restrict the future reservoir by the color of that subset together with `v_i` and the future vertex. Every `(k−1)`-subset is treated once, at its largest selected vertex. There are at most

    Σ_{i=1}^t binom(i−1,k−2)=binom(t,k−1)≤t^k

restrictions. A deletion subtracts one; passage to the largest of at most c color classes divides by at most c, with a ceiling. Thus after a restrictions and i deletions the reservoir is at least `N/c^a−i`, where `N=(t+1)c^(t^k)`. A further restriction preserves this lower bound with a increased by one because `−i/c≥−i`. Even at the maximum a it is at least `t+1−i≥1` for i≤t. There is no hidden loss from alternating deletion and restriction.

Color each `(k−1)`-subset of the first `t−1=R_{k−1}(s,c)` selected vertices by its common extension color into all subsequently selected vertices. An s-element set homogeneous for this induced coloring is homogeneous for k-subsets: take the first k−1 vertices of any k-subset and extend by its last vertex. There are enough vertices even when s=k. For k=2 the `(k−2)`-subset is the empty set, as needed.

For S, perform actual thinning in ascending arity k=1,…,a, from b_{k−1} to b_k. The frozen descending recurrence prepared exactly these sizes. Earlier homogeneity survives restriction. Both uses of S satisfy all domain assumptions: `(a,h,c)=(m,m,c₀)` and `(H,H,c₁)`. No unknown Ramsey constant is being substituted for the stated recurrence.

## 3. Quantitative separation and reversible chart transport

Source `eq:landmarks` (lines 637–661) has at most 8L interval endpoints and `(L+4n+1)Σ_{j=0}^n4^j` orbit-point expressions. This counts unreduced words, so coincidences and inverse cancellations only reduce the cardinality λ. Hence λ≤m. The four intervals used in author §2 lie in (0,1), have positive length and pairwise disjoint closures, exactly as required by `lem:action`.

Pad the finite landmark order to m elements if necessary. The number R of ordered same-length subtuple comparisons is at most

    Σ_{k=0}^m binom(m,k)² ≤ (Σ_{k=0}^m binom(m,k))²=4^m=r₀.

Removing trivial comparisons only decreases R. No additional factor for ordering is needed: each subtuple is increasing and already specified by its subset, while the ordered pair is counted by the square.

In source `lem:order-averaging` (lines 388–425), the space W_B has the sum of the component ℓ₁ norms. Its unit dual ball consists of lists of scalar functions f_ρ with each value in [−1,1], not lists with an extra factor R in each component. A partition of [−1,1] into bins of length at most `d₀=1/(20nr₀)` requires at most `40nr₀+2` bins. At any arity the list of at most R bin indices therefore has at most c₀ colors. B is fixed independently of the particular dual functional. The simultaneous Ramsey property supplies an m-set for every such functional, giving a chart C with

    |⟨f,v_C⟩|≤R d₀≤1/(20n)<1/(10n)=ε.

If the finite compact convex hull of the v_C had distance at least ε from zero, separating it from the open ε-ball would give a norm-one dual functional at least ε on every v_C, a contradiction. Thus some convex combination has W_B norm <ε. Each component difference of laws then has total variation at most half that sum norm, in particular <ε. Restricting padded charts to the actual landmark order preserves the required comparison laws; it does not require the partial action to extend to dummy landmarks.

For each positive letter s, the subtuples `h_s(D_s)` and `D_s` have the same length and their matching laws can be maximally coupled. Conditional sampling extends this to full charts with both marginals ν. Set `λ_{s⁻¹}(C,C′)=λ_s(C′,C)`. On the support of ν, choose a fresh uniform letter and then C′ with conditional probability `λ_s(C,C′)/ν(C)`. Marginal sums equal one. Stationary marked edge mass is `λ_s(C,C′)/4`, equal to its reversal's mass. Removing ν-zero states is legitimate because their incident positive masses are zero.

Consequently the four letters are independent and uniform across time before any conditioning on chart success; every step at stationarity matches all a∈D_s with failure probability at most ε. There are at most `binom(B,λ)≤B^λ≤A` states and `4A²` possible marked triples. Star has no fixed point because its letter changes to a distinct inverse, even on a chart loop. This checks author §2 against source `prop:chart-transport` (lines 432–497), including the figure's rank orientation `C′(a)=C(h_s(a))`.

## 4. Finite approximate spreading and the triangular lower bound

Reverse the original sequence and color its increasing k-subtuples at every arity k≤H using the norms on the grid `{-1,-1+1/J,…,1}^k`. Each norm is in [0,k]⊂[0,H], because the x_i have norm at most one. Bins of width η/2 need at most `ceil(2H/η)+2` choices, and there are `(2J+1)^k≤(2J+1)^H` grid points. Thus c₁ is sufficient. The Ramsey conclusion gives H distinct vectors retaining the reversed original order.

Let `N₀(a)=||Σ a_i x_i||_X` on ℝ^H, with shorter arrays padded by trailing zeros. This is a seminorm and satisfies `N₀(a)≤||a||₁`, hence `|N₀(a)−N₀(b)|≤||a−b||₁`. On two k-subtuples rounding coordinates in [−1,1] costs at most k/J on each side. Homogeneity of the color bins gives total oscillation at most

    η/2+2k/J≤η/2+2H/J≤η.

Scaling by `||a||∞` proves author (1), including zeros and arbitrary signed real coefficients. Comparisons involving zero coefficients remain valid because coloring was done at every arity, not merely at maximal support size. Removing or inserting internal zeros is an increasing-coordinate comparison after retaining their positions when necessary.

If `x_i=y_{j_i}` with `j₁>⋯>j_H`, the functional `f_{j_k}` is within σ of θ on i≤k and within σ of zero on i>k. Thus

    N₀(a)≥θ |Σ_{i≤k}a_i|−σ||a||₁

for each k, giving (2). The direction is correct for the reversed sequence. The same argument applies to each selected subtuple and to arrays with trailing zeros. It needs no independence of the x_i and no completion of X. A possibly nontrivial kernel of N₀ creates no problem.

## 5. Domains, random subsets, and the finite average

Fix one coefficient domain ℝ^(BQ). For `0≤j<T`, let `D_j:ℝ^(BQ)→ℝ^H` split every coordinate into Q^j equal consecutive pieces and then append trailing zeros. Its longest output is `BQ·Q^(T−1)=H`. The map

    U(a)=T^(−1/p)(Σ_i(D_j a)_i x_i)_{j=0}^{T−1}

is a single linear map on that fixed domain. Its ℓ_p^T(X) norm is precisely N in author (4). Short arrays are first padded by zeros, which does not change this formula. This supplies the fixed-domain interpretation explicitly stated in AUTHOR-CHECK, rather than using a different map for each path or each coefficient support.

For positive integers d_i≤e_i, choose d_i of the e_i slots uniformly in block i, place a_i/d_i there, and zero elsewhere. The expectation in each slot is a_i/e_i, also when a_i is negative or zero. Every sampled vector is an increasing placement of `F_d a` with the same ℓ₁ mass W=||a||₁. Convexity and (1) give (3) with additive error ηW. Independence of the block subset choices can be used, although only their marginals are needed for the expectation. Both endpoints and all sampled arrays fit in the stipulated H whenever (3) is invoked.

Refining an increasing placement of a by Q^j pieces gives another increasing placement into H: replace each original image position by its Q^j consecutive slots. Applying (1) scale by scale and the reverse ℓ_p triangle inequality proves (5), with error ηW. It is valid for two arrays of length at most BQ and for insertions of internal or trailing zeros.

Now take a of length at most B and 1≤d_i≤Q. The arrays `F_d a` have length at most BQ. At scale j their lengths are at most `BQ^(j+1)`, which never exceeds H. The extra endpoint `v_T=N₀(F_(Q^T)a)` uses length at most `BQ^T=H`, although it is outside the T-term definition of N. It is a valid N₀ value and is used only to compare the two finite lists.

Since the two iterated subdivisions replace each original a_i by `Q^j d_i` identical pieces, the random-subset comparison gives

    v_{j+1}−ηW≤w_j≤v_j+ηW,
    v_j=N₀(F_(Q^j)a),  w_j=N₀(F_(Q^j)F_d a).

No exact monotonicity or convergence rate is needed. All v_j are in [0,W]. Define `a₀=(T⁻¹Σ_{j=0}^{T−1}v_j^p)^(1/p)` and `a₁=(T⁻¹Σ_{j=0}^{T−1}v_{j+1}^p)^(1/p)`. Their p-th powers differ by `(v_T^p−v₀^p)/T`, with absolute value at most W^p/T. For nonnegative x≥y and p≥1, `(x−y)^p≤x^p−y^p`; hence `|a₁−a₀|≤W T^(−1/p)`.

The upper componentwise bound yields `N(F_d a)≤a₀+ηW`. Rewriting the lower bound as `v_{j+1}≤w_j+ηW` yields `a₁≤N(F_d a)+ηW`. Together these prove exactly

    |N(F_d a)−N(a)|≤δW,  δ=T^(−1/p)+η.

Negative lower bounds for an individual w_j cause no difficulty in this rearranged argument. The error is uniform over all coefficients and allowed multiplicities. The finite ℓ_p norm uses p≥1; the theorem's p>1 is more than sufficient. No extension of Markov type to an ℓ_p sum, finite representability of that sum, or completeness is assumed.

## 6. Adjacent merging: all signs and cancellation

Set W=||a||₁, τ=√η=ξ/24, and `e=2δ+2/Q`. For W=0 the assertion is immediate. Merging never increases ℓ₁ mass or length.

For uv≥0 and s=u+v, round u/s to r/Q (s=0 gives the zero pair). The rounded pair `(rs/Q,(Q−r)s/Q)` has the same total s, the same pair ℓ₁ mass |s|, and differs in ℓ₁ by at most 2|s|/Q≤2W/Q. For 0<r<Q, subdividing the pair into r and Q−r pieces, or the merged entry into Q pieces, produces the identical ordered array; all other coordinates have multiplicity one. Both source arrays have length ≤B and all multiplicities ≤Q. The two (6) errors total at most 2δW. For r=0 or Q the rounded pair differs from its merge only by insertion of zero, bounded by ηW≤2δW using (5). Therefore (8) holds in both directions with eW. Zero coefficients and negative same-sign pairs are covered.

For uv<0 and |s|≥τW, use symmetry to take s>0. If u>0>v, u=max(|u|,|v|) and

    (s,0)=α(u,v)+(1−α)(0,s),  α=s/u≥s/W≥τ.

If v>0>u, interchange the two endpoints. With all other coefficients fixed, let M be the norm of the merged array. Each endpoint pair with its inserted zero has norm between `M−ηW` and `M+ηW`; its ℓ₁ mass is at most W. Convexity at the nearer endpoint gives

    M−ηW≤αN(a)+(1−α)(M+ηW),
    M≤N(a)+(2−α)ηW/α≤N(a)+2τW.

Thus the stated α is correct, is bounded away from zero in this case, and the argument requires only endpoint comparisons, not constancy of N over a same-sign segment.

For |s|<τW, change v by at most τW to make s′ equal to sign(s)τW, choosing +τW when s=0. Then W′≤(1+τ)W. Lipschitz continuity costs at most τW on the original side and τW on the merged side. If the new pair has the same sign, the cost is at most `eW′+2τW≤(2e+6τ)W`. If it still has opposite signs, the endpoint computation costs at most

    2η(W′)²/|s′| ≤ 2(1+τ)² τW.

Adding the perturbation gives `[2(1+τ)²+2]τW≤(41/8)τW<6τW`, since τ≤1/4. This includes exact cancellation s=0 and all possibilities that the perturbation creates a zero or changes a sign.

The combined bound is the submitted

    ζ=2e+6τ=4δ+4/Q+6√η.

The ceilings give `T^(−1/p)≤ξ/16` and `1/Q≤ξ/16`, so

    ζ≤3ξ/4+ξ²/144≤ξ.

All constants are valid uniformly in p,n,θ. A consecutive partition of a length-B array uses at most B−1 mergers, safely bounded by B; every intermediate ℓ₁ mass is at most its original mass. Hence total error ≤BξW. No accumulated factor depending on Q, T or the number of coordinates of U is missing.

## 7. Source labels, exact ranks, and robustness losses

The source action, `lem:two-levels`, and transport identities are used with their actual finite landmark domains. A positive marked edge has exactly the raw label in source `eq:labels`, a sum of L ordered differences. A negative edge is defined as the negative of its reversed positive edge. Thus labels are odd even on marked loops and on chart transitions that fail matching. Their coefficient arrays lie in the first B coordinates, each has total coefficient sum zero, and each has ℓ₁ mass 2L.

Put `D_k=N((1,−1)^k)`. Every refined copy of `(1,−1)^L` has ℓ₁ mass 2L and a prefix sum equal to 1 at the end of its first positive block. The triangular estimate gives `N₀≥θ−2Lσ=θ/2` at every scale, hence `D_L≥θ/2>0`. Approximate spreading gives `N(g(e))≤D_L+2Lη≤2D_L`, using `2Lη≤2Lξ=θ/(2048B)≤θ/2`. Negative labels use symmetry, not another uncontrolled comparison.

For completeness, the actual source rank interface is as follows (lines 686–783). For an all-matching n-step path, write w=s₁⋯s_n, let its reduced length be ℓ>0, and write `h_w(0)=q+z`, q an integer and 0<z<1. Displacement <2 per letter gives `−2n≤q≤2n−1`. For integer `a=L/4≤j≤b=3L/4`, the two initial points j and z+j and their successive inverse images belong to Λ. The trajectories have the forms

    h_(s_i⁻¹⋯s₁⁻¹)(0)+j,
    h_(s_(i+1)⋯s_n)(0)+j−q.

Their words have length at most n and their shifts lie in [−2n,L+2n]. The displacement estimate places every trajectory point between j−2n and j+1+2n, inside (0,L): indeed a=2n+2 and b=6n+6. Therefore all needed partial maps are defined, including at endpoints i=0,n. Matching transports the rank unchanged, `C_i(y_i)=C₀(y₀)`.

For `G=Σ g(E_i)`, a positive difference contributes to a prefix at C(y) precisely the half-open indicator `1_[α,β)(y)`. Positive steps therefore contribute `1_A_s(y_(i−1))`. Negative steps are read in the terminal chart and contribute `−1_A_(s⁻¹)(y_i)=1_A_s(y_(i−1))−1`. Hence the prefix sum is the exact cocycle c_w(y₀). The cancellation identity eliminates inverse adjacent letters in this scalar cocycle; G itself still contains all n labels. This distinction is essential and is maintained in the proof.

At `r_j=C₀(j)` and `t_j=C₀(z+j)` the prefix levels are `V₀=−n₋` and `U₀=n₊`, where n₊+n₋=ℓ. Thus `r_j<t_j<r_(j+1)`, `U₀−V₀=ℓ`, and `|V₀|,U₀≤ℓ`. Also `||G||₁≤2Ln`, and its total sum is zero.

Use cuts `0,r_a,t_a,r_(a+1),…,t_(b−1),r_b,B`. Their consecutive differences give

    h=(V₀,(ℓ,−ℓ) repeated L/2 times,−V₀).

There are exactly b−a=L/2 inner pairs, not L/2+1. The first block is nonempty since r_a≥1; all middle cuts are strict; the last block is nonempty because `r_b<t_b≤B`. The output length is L+2≤B. The compression estimate gives `N(G)≥N(h)−E` with `E=2BLnξ`.

The interior of h has norm at least `ℓD_(L/2)−ηℓL`, as it is an increasing placement of L alternating entries. The endpoint array has norm at most `|V₀|D₁+2η|V₀|`. Subtraction by the triangle inequality gives exactly author (12):

    N(G)≥ℓ(D_(L/2)−D₁)−E−ηℓ(L+2).

For the one-cut bound choose, for example, r_a and t_a. They are strictly between 0 and B, since `t_a<r_(a+1)≤r_b<B`. Both compressed arrays have two entries and no placement error: `(V₀,−V₀)` and `(U₀,−U₀)`. Thus (13) gives

    N(G)≥max(|V₀|,U₀)D₁−E≥(ℓ/2)D₁−E.

This explicit permissible choice avoids any issue with taking a terminal cut at B. It is a specialization of the cuts already offered in the submitted proof, not a repair of its construction.

For nonnegative d,b, `max(d−b,b/2)≥d/3`. Apply this with `d=D_(L/2)` and `b=D₁`, and bound both branch errors by `E+ηℓ(L+2)`. Splitting the L-pair array into two halves gives `D_L≤2D_(L/2)+ηL`, since only the second L-entry block is a placement. Therefore

    N(G)≥ℓD_L/6−E−ηℓ[(L+2)+L/6]
         ≥ℓD_L/6−E−2ηn(L+2),

which verifies (14) with slack. Using B≥3, L≥16, η≤ξ,

    E+2ηn(L+2)≤2BLnξ+6Lnξ
                    ≤4BLnξ=θn/1024
                    ≤θn/96≤nD_L/48.

This verifies (15), including the direction of the last inequality from `D_L≥θ/2`. No exact-norm source conclusion has been applied to an approximate seminorm. The source supplies only the scalar geometry and labels; all pertinent norm losses were accounted for explicitly.

## 8. Probability, including n=1

Before conditioning on success the successive letters are independent uniform elements of four inverse-paired letters. When reduced length is positive, exactly one letter cancels, so its conditional drift is `(3−1)/4=1/2`; at zero the next length is one. Consequently `Eℓ≥n/2`, while 0≤ℓ≤n. With `P_n=P{ℓ≥n/4}`,

    Eℓ≤n/4+nP_n,

so `P_n≥1/4`. The weak estimate suffices; no asymptotic limit or large-n qualification is used. Stationarity of the chart chain makes each matching-failure probability at most 1/(10n). The union bound gives total failure probability at most 1/10. It needs no independence between success events or between success and length. Their intersection with ℓ≥n/4 has probability at least `1/4−1/10=3/20`.

On that intersection (14) and (15) give

    N(G)≥(n/4)D_L/6−nD_L/48=nD_L/48.

For n=1 the same drift and probability estimates remain valid, L=16 has integer quarter-cuts, and ℓ≥n/4 implies ℓ>0. No endpoint exception is concealed.

## 9. Finite reflected lattice and the same-chain potential

Let r be the number of two-element star orbits among positive-probability marked edges. There are at most `4A²` oriented marked triples, so `1≤r≤2A²`. The support of the chart law is nonempty and has outgoing transitions; the fixed-point-free letter involution gives r≥1. Choose one representative e_j from each orbit and give e_j displacement +u_j in ℤ^r and its reverse −u_j. Even a marked chart loop has nonzero lattice displacement and a distinct reverse mark. Zero labels may be assigned such a coordinate without harm.

Set `R=4nA²`, an integer >n, and use states `(C,a)` with `a∈{−R,…,R}^r`. Propose an original marked transition at C. Accept its chart and lattice move if inside the cube; otherwise retain both C and a. Under `ν⊗Unif(cube)`, an accepted directed move and its reverse have equal mass

    ν(C)q(e)/(2R+1)^r = ν(C′)q(e*)/(2R+1)^r.

An accepted reverse always exists when the forward move is accepted. Rejections contribute only diagonal probabilities. Summing marked probabilities yields a genuine unmarked transition matrix with nonnegative entries and row sums one, reversible with this probability law. Detailed balance also implies stationarity. Multiple edges or accepted/rejected self-loops cause no defect.

The number of states is at most

    A(2R+1)^r≤A(8nA²+1)^(2A²)=C(n).

There is no dependence on p, θ, X, or the multiplicities in the coordinate average. State probabilities may be arbitrary positive real numbers and need not be uniform on charts, as allowed by the frozen theorem.

Define on these states

    Ψ(C,a)=U(Σ_j a_j g(e_j)).

The array in parentheses is in the first B coordinates of the same fixed domain of U, however large its coefficients. Linearity gives increment U(g(e)) on an accepted edge and zero on rejection. Ψ ignores C in its formula; this is legitimate because the lattice coordinates record marked edge identities. It follows that its expected one-step p-cost in V=ℓ_p^T(X) is at most `(2D_L)^p`.

Independently choose the initial lattice coordinate uniformly. If it is in `{−R+n,…,R−n}^r`, every possible sequence of n proposed moves stays in the cube. Couple to an original stationary chart trajectory by the same proposals until the first rejection. On this interior event no rejection occurs; it is independent of the entire original trajectory. Its probability satisfies

    α=(1−2n/(2R+1))^r≥1−2nr/(2R+1)>1/2,

because `2nr≤4nA²` and `2R+1=8nA²+1`. This uses the integer Bernoulli inequality and the strict +1 in the denominator. It does not assert independence of lattice coordinates after evolution or independence of rejected-path proposals from the interior event.

The displacement of Ψ on the coupled event is U(G). Thus its n-step p-cost is at least

    (3/40)(nD_L/48)^p.

This is an actual finite chain and a finite-valued map. Neither an infinite-volume limit nor a nonstationary infinite group walk is substituted for it.

## 10. Coordinate extraction into the original X

Write Ψ=(Ψ₀,…,Ψ_(T−1)), including the scale `T^(−1/p)` in each coordinate. On this same finite chain let v_j and u_j be its one-step and n-step p-costs in X. Finite summation gives

    Σ_j v_j≤(2D_L)^p,
    Σ_j u_j≥(3/40)(nD_L/48)^p
            ≥[(3/40)(n/96)^p] Σ_j v_j.

The direction of the last comparison is correct: multiply the upper bound for Σv_j by the proposed ratio. If Σv_j=0, each nonnegative coordinate one-step cost is zero. Stationarity then implies every consecutive increment through time n is zero almost surely; a finite union of null events suffices. Hence all u_j are zero, contradicting the strictly positive displayed n-step lower bound. The same argument separately gives `v_j=0 ⇒ u_j=0`.

It follows by weighted averaging that some j with v_j>0 satisfies

    u_j/v_j≥(3/40)(n/96)^p.

Otherwise summing the finitely many strict opposite inequalities with positive weights contradicts the preceding ratio estimate. Set `F=Ψ_j/v_j^(1/p)`. This has one-step p-cost exactly 1 and the stated n-step lower bound. Every Ψ_j value is a finite real linear combination of the selected x_i and hence of the original y_i. Only scalar multiplication in the original X-norm was used; there is no claim that V embeds into X or is finitely representable in X. This completes Theorem A without an unproved return from an auxiliary space.

## 11. Strict Markov contradiction and full J-convexity conversion

For Corollary B set

    n_*=ceil(((40/3)(96K)^p)^(1/(p−1)))+1,
    L_*=8(n_*+1),  M_*=M(p,n_*,1),  ε_*=1/(4L_*).

Since p−1>0, `n_*^(p−1)>(40/3)(96K)^p`. Theorem A at θ=1, if its array existed, would give a finite reversible stationary chain with normalized cost 1 and

    E||F(Z_n*)−F(Z₀)||^p ≥ (3/40)(n_*/96)^p > K^p n_*.

The middle-to-right inequality is strict, so it contradicts the assumed Markov inequality, even if its upper bound is attained. Thus such an array of length M_* and entry error at most ε_* cannot exist.

Assume all admissible signed sums of some unit-ball vectors x₁,…,x_M have norm >M−ε_*, where M=M_*. This is exactly the negation of the frozen conclusion with its non-strict ≤ sign. These sums are nonzero because M≥1 and ε_*<1. Real Hahn–Banach supplies a norming g_j of norm one (norm at most one suffices) for each `S_j=Σ_(i≤j)x_i−Σ_(i>j)x_i`, j=1,…,M. On each summand its signed evaluation is ≤1, so all deficits are nonnegative and their total is `M−||S_j||<ε_*`. Every individual deficit is therefore <ε_*. Hence g_j(x_i) is within ε_* of +1 when i≤j and of −1 when i>j.

Put g₀=−g_M. This norms S₀=−S_M and has the required all-negative evaluations. Define

    f_j=(g_M−g_(j−1))/2,  1≤j≤M.

Then `||f_j||≤1`. For i<j, both evaluations approximate +1, so `|f_j(x_i)|<ε_*`. For i≥j, their reference values are +1 and −1, so `|f_j(x_i)−1|<ε_*`. For j=1 this reduces to f₁=g_M, including its endpoint case. For j=M it correctly singles out the last vector after the near-zero preceding entries. This is precisely the forbidden orientation `1_(j≤i)`, with even strict error <ε_* and thus certainly the required ≤ε_*.

The contradiction proves an admissible j in 0,…,M with `||S_j||≤M−ε_*`; division by M yields normalized deficit ε_*/M. Hahn–Banach on a real normed space does not require completeness. All other operations used finitely many vectors, finite probability spaces, and finite-dimensional coefficient spaces. Thus finite-dimensional, incomplete and nonseparable spaces are covered. For X={0}, Theorem A's hypothesis is impossible since θ>σ at a diagonal entry, and Corollary B is immediate. K≥1 is the frozen assumption; no stronger bound or renorming conclusion has been inserted.

## 12. Strongest source/classical comparisons and their relevance to correctness

The source appendix already contains reversed triangular arrays, Ramsey spreading extraction, random-subset subdivision monotonicity, and convex adjacent merging. Its main proof already supplies the marked reversible chart construction, two-level obstruction, and reflected lattice lift. The explicit finite replacement here follows those actual operations, not merely the qualitative superreflexivity headline. Sections 2–11 of this review carry that compatible composition through the exact frozen constants. Finite averaging and coordinate selection discharge the two places where an unquantified limit or a false assertion about finite representability of ℓ_p^T(X) would otherwise leave a bridge.

The actual [NPSS author-hosted 2004 proof](https://web.math.princeton.edu/~naor/homepage%20files/Mtype.pdf), §§2 and 4, was read: it uses forward and reverse martingale increments, a specified power-smoothness estimate, and stationarity to bound their costs. It provides a forward smoothness-to-Markov estimate, not a same-p quantitative converse or a distortion bound used here. The actual [Naor–Peres v3 proof](https://arxiv.org/abs/0708.0853v3), §§2 and 5, separates cocycle estimates for an identity-started group walk from stationary finite-chain Markov type, and treats bounded-increment compression composition. The present proof does not confuse these interfaces.

[Ostrovskii–Randrianantoanina §2.1](https://facpub.stjohns.edu/ostrovsm/OstRandESA.pdf) explicitly gives the ESA/SA/spreading relationships and the triangular-array-to-spreading-to-ESA finite-representability route. [Pisier's notes §3.3](https://webusers.imj-prg.fr/~gilles.pisier/ihp-pisier.pdf) contain the additive subdivision limit, signed-sum J-convexity construction, and norming-functional argument. The entire section, through its actual §3.4 boundary, was read. Its displayed absolute-value signs in (3.34) and (3.36) were independently recovered from rendered pages. The printed δ′(m) line on p.73 uses m although its preceding normalization gives denominator r(m); that line supplies no numerical estimate in this review or the submitted finite proof. The compatible qualitative consequence follows from the preceding displayed inequality when r(m)→∞. No unexamined numerical rate is imported from those notes.

A further actual primary comparison was read in full: [Wenzel, arXiv:math/9710204v1](https://arxiv.org/abs/math/9710204v1), *Superreflexivity and J-convexity of Banach spaces*. Its proof uses individual Hahn–Banach deficits and a near-triangular factorization, and its finite Ramsey argument uses two consecutive thinnings of interval configurations, norm bins, and interlaced interval averages to obtain J-convexity information at a smaller order. This confirms that finite quantitative Ramsey/J-convexity operations must be credited in any contribution review. I do not substitute Wenzel's theorem, hypotheses, or bound for the frozen witness statement; the correctness reconstruction above already verifies the submitted construction.

The original Brunel–Sucheston 1975 paper could not be retrieved at either exact AMS PDF route in this review (both HTTP 403). That is a remaining original-primary access limit, not evidence of absence, novelty, impossibility, or a gap in the self-contained finite estimates above. I make no exhaustive literature or world-priority finding and no contribution grade. The two admitted i88 original-history sections were read at their exact byte ranges and retain their original binary-diamond/compatibility scopes; the i104 modular-representation subsection is an unrelated semantic false admission, not a premise. No old closed target was reopened or renamed.

## 13. Essential-objection register and disposition

No essential objection remains. Specifically, the following possible failure modes were tested and resolved in the unchanged argument:

- Reservoir exhaustion or reversed thinning order: resolved by the explicit `N/c^a−i` invariant and ascending execution of S.
- Too many chart comparisons or wrongly normalized separation dual: resolved by `R≤4^m` and the sum-norm dual description.
- Applying exact-spreading source conclusions directly to N: avoided by the separate scalar interface and full error computation (12)–(15).
- A missing j=T endpoint or non-linear varying-domain U: resolved by H=BQ^T and one fixed padded ℝ^(BQ) domain.
- Same-sign endpoint r=0,Q, tiny nonzero sums, or exact cancellation: all covered in the explicit ζ estimate.
- An empty final block, off-by-one oscillation count, or illegal one-cut compression: the actual ranks give L/2 pairs and allow strict interior cuts r_a,t_a.
- Conditioning letters on chart success or assuming independent matching failures: neither is needed; stationarity plus an unconditional length bound suffices.
- Marked loops, nonuniform chart mass, or rejected chart moves breaking reversibility: the full-state reflected lift preserves exact detailed balance.
- A coordinate of zero one-step cost with nonzero long cost, or extraction on another chain: stationarity excludes the former and all coordinates use the same finite chain.
- Non-strict Markov contradiction or a reversed triangular orientation from signed sums: the +1 in n_* and the formula for f_j settle these cases.

The explicit fixed-domain notation, lower-average rearrangement, and choice r_a,t_a above expose routine details already present or allowed in the submitted proof. They require no mathematical repair. No change to FROZEN.md, DERIVATION.md, the array length, the state bound, the probabilities, the original norm, or the space class is requested.

The indicated Lean documentation's scope description is not proof coverage. The actual comparator `lean/ComparatorChallenges/MarkovType.lean` ends its theorem with `sorry`; no formal support for this review or the frozen result is claimed. Artifact verification and the copied controls in the outside report establish identity only. Reading, access, isolation, rights, and final detached-anchor boundaries are documented in [the outside report](../REPORT.md).
