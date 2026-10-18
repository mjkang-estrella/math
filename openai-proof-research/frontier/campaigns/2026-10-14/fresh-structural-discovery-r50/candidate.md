# T239A: the exponential singularity rate of a loopless random graph

Complete author-side candidate at original-scope.txt. Upstream results and lower operations are stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No independent proof or contribution verdict is claimed.

## Theorem

Fix a real p∈(0,1). Let A_n be the real adjacency matrix of the simple loopless graph G(n,p). Then

    lim P(det A_n=0)^(1/n) = R_p := max{1-p,p²+(1-p)²}.

All limits in this text hold with p fixed. There is no uniformity for varying p, no prefactor or conditional classification claim. Write q=1-p, r=max(p,q), Q=p²+q², a=-log₂r and h=-p log₂p-q log₂q. Then r²<Q and 2^{-h}≤Q, with equality in the second relation exactly at fairness.

The lower bound is elementary: vertex1 is isolated with probability q^{n-1}; rows1 and2 agree if their common edge is absent and their exterior neighborhoods agree, an event of probability q Q^{n-2}. Each event makes A_n singular. It remains to prove the upper bound.

## 1. Exact source inputs

Use the biased companion *The sharp singularity rate for biased symmetric sign matrices* (October4,2026), abbreviated B, and the uniform companion (October3), abbreviated U. B gives a bit-model analysis with independent upper entries of probabilities t or1-t, rank-at-most-two mean, and reference sizes N-N^{7/10}≤m≤N. Its lower arguments use t∈(0,1/2), maximum atom1-t, and common variance t(1-t). We will also use those arguments at t=1/2: Sections3–6 use only positive variance, a maximum atom below1, and the displayed entropy margins internal to the lattice construction. The strict inequality h>−log₂Q is used only in B's final sign-model reduction, not in these lower arguments. At fairness its lattice Fourier factor, moment estimates, layer costs and path bound remain valid with maximum atom1/2. The corresponding uniform lattice and algebraic operations are also stated in U.

Here are the precise lower inputs, with ell=log log N. “Typical” means failure at most2^{-N f(N)} with f(N)→∞, uniformly over the reference sizes.

1. B, Section3: uniform prime corank, low-height rational-subspace cover, determinant-minimizing saturated sublattice, projected lattice point count. Section4's simultaneous lattice theorem says that for fixed D>0 and α>0, every intermediate lattice B Z^m⊂K⊂Z^m of index at least N^{N ell^{-D}} has fewer than2^{αN} cube points in every coset, typically.
2. B, Section5: define G_B=Z^m/BZ^m for nonsingular B, layer heights k_B(l,j), weights ν_l=(log_N l)/N, W_s=Σ(k_B-s)_+ν_l, T₂=Σ_{k_B=2}ν_l and J_B=Σ_{k_B≥3}k_Bν_l. Then J_B≤3W₂ and the total height-weight is at most1/2. Isotropic discriminant classes admit the stated colors; differences in one overall color generate a subgroup whose restricted pairing image has order at most N^{NJ_B}. If T₂ is not small, subexponentially many color subgroups have sufficiently large index for input1. If T₂ is small, the total color count is subexponential.
3. B, Section5: robust extraction loses o(N) logarithmic cardinality. A rational injective image of a robust cube set with difference diameter O(sqrt(N)) has lattice covolume exp(O(N ell)); its original difference span has height exp(O(N ell)). For a rational pairing on a lattice L with radical lattice K and pairing-image order T, the determinant on the orthogonal complement of the radical is at least (det K)²/[T(det L)²].
4. B, Section5: typically, simultaneously for every rational F of height≤exp(N ell²), rank(B^{-1}|F)≥dim F−ξN. Also, for every ξ>0 some fixed w>0 gives at most ξN eigenvalues of B in [-w sqrt(N),w sqrt(N)], typically. The first assertion is about restrictions of bilinear forms, including matrix-selected spans.
5. B, Section6: every nonsingular bit matrix has a principal deletion path of steps1 or2; each width-two deletion has cross columns v satisfying vᵀC^{-1}v∈{0,1} and ||C^{-1}v||∞≤1. The retention lattice, symmetric tail recursion, and terminal-window alternative are deterministic. On a fixed forward path, a costly retained-layer event has probability at most r^{N-o(N)}; a width-two gate at a typical node of small W₂ costs r^{2N-o(N)}. There are2^{o(N)} paths. High-layer failures are superexponentially small. The resulting estimate is

    P(B nonsingular, W₂(B)>ζ) ≤ r^{2N-o(N)}              (1.1)

for each fixed small ζ permitted by the static column estimate; more explicitly the source bound is2^{-N(2a-10e)} with arbitrary sufficiently small fixed e>0.

The two companions supply the difficult arithmetic and probabilistic operations in these inputs. We do not reprove or audit them. Section2 below changes the graph metric in input3; Sections3–4 explain the distribution and kernel interfaces rather than claiming an unqualified source corollary.

## 2. Projected graph columns

Fix a coordinate j and L≥1. For invertible symmetric bit B define

    S_{L,j}^*(B)={z∈{0,1}^m: zᵀB^{-1}z∈{0,1},
                          ||P_j B^{-1}z||₂≤L sqrt(N)},

where P_j deletes coordinate j. The missing inverse coordinate has no prescribed bound. We prove the analogue of B's static column estimate: for every e>0 there is ζ>0 such that typically,

    W₂(B)≤ζ ⇒ |S_{L,j}^*(B)|≤2^{eN},                 (2.1)

simultaneously for all j. Typical events will be exactly the source's simultaneous lattice, inverse-rank and spectral events.

If T₂≥ell^{-12} up to the source's rounded R=ceil(ell²) convention, B's height-two color-subgroup argument applies verbatim: it requires cube membership and isotropic class, not an inverse norm. It proves the subexponential bound using input1. Retain the source's exact threshold σ=R^{-6} in this case distinction.

In the other case partition S_{L,j}^* first by the bit z_j and then by the source colors. Choose a largest part and robustly extract V. The bit partition costs at most1 in base-two logarithm; the colors and extraction cost o(N). Thus

    log₂|S_{L,j}^*|≤log₂|V|+o(N).

Its difference span F lies in E={x:x_j=0}. Put C=B^{-1}. Define the global rational linear map Φ(x)=(x,P_j Cx) on R^m and let γ'=Φ|E. The robust-image lemma is applied to the affine restriction Φ|aff(V), which is injective. For v,v'∈V,

    ||Φ(v)-Φ(v')||²=||γ'(v-v')||²≤m+4L²N.

The source robust-image lemma gives det L_V≤exp(O_L(N ell)) for the lattice of these image differences, and H(F)≤exp(O(N ell)). On Γ'=γ'(E) define q_B(γ'x,γ'y)=xᵀCy. Because x_j=0,

    |q_B(γ'x,γ'x)|≤||x|| ||P_j Cx||≤(1/2)||γ'x||².    (2.2)

Thus the self-adjoint operator of this form in the projected graph metric has norm at most1/2. This bound would generally fail without fixing the input bit before taking differences.

There is a simpler spectral description than a general finite-codimension comparison. Identify E with R^{m-1} and put C_E=(B^{-1})_{j^c,j^c}. Since x_j=0, γ'(x), after dropping its identically zero input coordinate, is exactly (x,C_E x). The form is xᵀC_E y. Diagonalizing the symmetric compression C_E shows that its graph-metric eigenvalues are

    λ/(1+λ²),  λ an eigenvalue of C_E.

Suppose B has at most ξN eigenvalues in [-w sqrt(N),w sqrt(N)]. Then C=B^{-1} has at most ξN eigenvalues with absolute value greater than1/(w sqrt(N)). Cauchy interlacing, applied to the positive and negative tails separately, gives the same upper bound for the principal compression C_E. Hence all but at most ξN graph-metric eigenvalues have absolute value at most1/(w sqrt(N)); all have absolute value at most1/2. This compression need not be invertible. No diagonalization simultaneously compatible with C and the coordinate projection is assumed.

The restricted form on γ'(F) has rank s≥dim F−ξN by input4. Its pairing modulo Z is the same pullback of the discriminant pairing on the subgroup generated by the original differences. Hence its image order is at most N^{NJ_B}. The first-coordinate projection of its radical lattice is an integer lattice of the same rank, and contracts volume; the radical lattice consequently has covolume at least1. Input3 gives

    |det(q_B on the radical complement)|
      ≥ N^{-NJ_B} exp(-O_L(N ell)).

By (2.2), the spectral bound, and the exterior-power bound on the determinant of a compression of a self-adjoint operator, the same determinant is at most

    (1/(w sqrt(N)))^{(s-ξN)_+}.

Comparison gives dim F/N≤2J_B+2ξ+o(1), also when s≤ξN. Coordinate projection gives |V|≤2^{dim F}. Since J_B≤3W₂, choosing ζ,ξ with6ζ+2ξ<e proves (2.1). All exceptional events are simultaneous in F and independent of j; the error is uniform in j. A union of all m such column sets would only cost a further log₂m, though we use fixed j below.

## 3. Fixed diagonal and the column probability estimate

Let B have independent Bernoulli(p) off-diagonal entries and any prescribed bit diagonal. Its auxiliary version with independent Bernoulli(p) diagonal has mean p times the all-ones matrix and belongs to B's bit model, taking t=min(p,q). The probability that its diagonal equals the prescribed pattern is at least min(p,q)^m=exp(-O_p(N)). Conditioning therefore preserves every typical input in Section1, and consequently the projected static estimate (2.1). This is uniform over all deterministic diagonal patterns. We never obtain a sharp exponential estimate by dividing the source's final exponential bound by this diagonal probability.

Instead repeat the last, forward-exposure path argument on the fixed-diagonal ensemble. Every nonsingular principal minor is a bit matrix and has the same gated deletion paths. Each cross column consists only of independent off-diagonal Bernoulli(p) bits, even when all diagonal entries are fixed. Its point mass is at most r^m. The retention lattices are fixed before the column is exposed. Thus the source conditional cost estimates, high-layer exponential moment and terminal-window alternative hold without change. At a width-two gate the two cross columns are conditionally independent; their mutual entry belongs to the new2×2 block and is not included in either cross column. The original full-norm static estimate, also typical after conditioning, bounds these gates. Nothing requires choosing the backwards path independently of the matrix: as in the source, fix all paths first, expose each forwards, and only then union over2^{o(N)} paths.

It follows that for every sufficiently small e>0, uniformly over prescribed diagonals and j,

    P(B nonsingular, |S_{L,j}^*(B)|>2^{eN})
        ≤2^{-N(2a-10e)}                              (3.1)

eventually. To align constants, use (2.1) with a smaller e and its ζ, run the source path proof with that static threshold, and absorb the fixed slack in10e. The final implication is: on W₂≤ζ the projected static set is small, and W₂>ζ has the same two-column path cost. Fairness causes no issue here: a=1 and all strict comparisons in these paths are against small e>0, not against Shannon entropy.

## 4. Kernel reduction for arbitrary prescribed bit diagonals

Let A have iid Bernoulli(p) off-diagonal entries and an arbitrary deterministic bit diagonal d. We establish a corank-one probability bound uniformly in d.

A zero column has probability at most q^{n-1}; a union costs at most n q^{n-1}. If no column is zero, choose a nonzero kernel vector v and an anchor j with largest absolute coordinate. Its tail off j is nonzero, so normalize that tail to norm1. Some entry A_{kj}=1; the kth row equation then yields

    |v_j|≤Σ_{l≠j}|v_l|≤sqrt(n-1).                    (4.1)

This includes k=j. It is important that a zero column was removed; the diagonal itself need not be nonzero.

The source's normalized-tail compressibility estimate now applies with the following explicit changes. Set W=A-p11ᵀ; its deterministic diagonal is bounded by1. A quadratic-form net and Hoeffding give P(||W||>L sqrt(n))≤2^{-4n} for a sufficiently large fixed L. Approximate a tail supported on at most λn coordinates by a fixed δ-net, approximate the anchor on [-sqrt(n),sqrt(n)], and approximate Σv_l by a separate scalar. The mean matrix p11ᵀ is thereby paid by one scalar, exactly as in B's proof. The residual is O(Lδ sqrt(n)). In each test row outside the approximate support and anchor, all coordinates tested are independent Bernoulli(p) bits; the diagonal contributes zero because the approximate vector vanishes there.

For two significant coefficients, two outcomes differing in only one bit are separated by the absolute value of that coefficient. An interval of length2w smaller than both absolute coefficients therefore contains at most two opposite vertices of the bit square, whose probability is at most Q. For example, after the source threshold u₀ gives coefficients at least u₀/2, choose w<u₀/8; this adjusts the sign-to-bit scale. If all tail coefficients are small, their variance is pq times a quantity bounded below, and the source's unequal-summand Berry–Esseen argument makes the small-interval probability less than Q. Thus every row test has probability≤Q, uniformly over the scalar shift. Tests in different outside rows use disjoint cross-block entries. The source entropy/net argument, choosing γ,δ,λ in that order, gives for every ε>0

    P(a nonzero kernel vector has a compressible normalized tail,
      and A has no zero column) ≤2^{εn}Q^n.           (4.2)

All constants are fixed before n, may depend on p,ε, and are uniform in d. This is a normalized-tail statement, not an assertion that a full normalized kernel vector cannot lie near a coordinate vector.

On the remaining corank-one event, every such tail has at least λn/2 coordinates of magnitude≥c/sqrt(n), for a fixed c∈(0,δ). With failure exp(-Ω(n²)), fewer than λn/4 rows have off-diagonal one-count outside p(n-1)±wn, for any fixed w>0. The proof is B's row-count argument: a fixed linear-size set of deviating rows gives an order n² deviation in independent upper-triangular variables with coefficients1 or2. Diagonal patterns alter counts by at most1 per row.

Choose a tail coordinate i≠j of magnitude≥c/sqrt(n) whose row count is typical. Because A has corank one, its adjugate is a nonzero multiple of vvᵀ. Deleting i leaves a nonsingular principal minor B, and with z the deleted cross column,

    B^{-1}z=-v_{[n]\setminus{i}}/v_i,
    zᵀB^{-1}z=d_i∈{0,1}.

After deleting the anchor coordinate j from this inverse image, its norm is≤sqrt(n)/c. Hence z∈S_{L,j}^*(B) for a fixed L≥2/c. This is precisely where the projected graph count is used. The full inverse image need only have norm O(n); using the source's full graph bound here would be unjustified.

For fixed i,j, B is independent of z. A specified z with s ones has point probability p^s q^{n-1-s}. Its compatibility with the selected row's typical count implies |s-p(n-1)|≤wn, so this probability is at most2^{-n(h-C_pw-o(1))}. Use (3.1) for B with reference N=n and m=n-1. Away from its exception, at most2^{en} columns are possible, and their total mass is at most2^{-n(h-e-C_pw-o(1))}. Union over i,j costs only n². Combining with zero columns, (4.2), row-count failure and (3.1) gives, uniformly in d,

    limsup P(rank A=n-1)^(1/n)
       ≤ max{q,Q,2^{-h},r²}=R_p,                     (4.3)

by taking ε,e,w arbitrarily small. At p=1/2, 2^{-h}=Q; no strict entropy gap is necessary for an exponential-rate limit.

## 5. Corank reduction without random diagonal entries

For the original zero-diagonal A_n, a corank at least t=ceil(n^{3/5}) has probability2^{-Ω_p(n^{6/5})}. Indeed, expose a maximal nonsingular principal block and its cross block. The remaining principal Schur complement is forced. Its off-diagonal entries alone cost at most r^{k(k-1)/2} when its size is k; the deterministic diagonal need not be charged. Union over principal sets and k≥t gives the assertion.

For 1≤k<t, the source's deterministic diagonal-flip lemma chooses k-1 coordinates whose coordinate functionals are independent on ker A_n. Changing those diagonal zeros to ones produces corank exactly one. The proof is unchanged: pairing (A+D)y=0 with ker A forces the selected y-coordinates to vanish, and the remaining kernel is precisely the one-dimensional intersection with those coordinate hyperplanes.

There are at most Σ_{j<t}binom(n,j)=2^{o(n)} possible changed-diagonal patterns. For each fixed pattern, the off-diagonal array, and therefore its probability, is unchanged by this map. Consequently

    P(det A_n=0)
      ≤2^{-Ω_p(n^{6/5})}
        + Σ_{|I|<t} P(rank(A_n+diag(1_I))=n-1).

The uniform bound (4.3), with all finite-n bounds uniform in the diagonal pattern, gives limsup≤R_p. Together with the two elementary lower events this proves the full frozen theorem.

## Contribution boundary

The random-lattice theorem, finite-pairing colors, robustness/determinant estimate, low-height uniformity, principal-minor path and two-column probability gain are source operations. Fixed-diagonal conditioning of superexponentially good events and deterministic diagonal-pattern enumeration are routine transfers. Tail nets and Shannon row pricing are adapted source operations.

The only proposed new construction is the bit-fiber restriction combined with an omitted inverse coordinate in the graph lattice, retaining both the finite pairing determinant and a uniformly bounded indefinite form. It permits a typical off-anchor deletion for adjacency kernels whose full normalized vector may be dominated by its anchor. Whether this finite-codimension repair is substantial rather than technical requires an independent contribution assessment. The theorem's sharp rate does not decide that question. This does not resolve the prior I132/I135 leading-prefactor/conditional-classification target.
