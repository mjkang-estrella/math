# Independent adversarial proof audit r1: full theorem F

**Verdict: PASS.** This verdict applies to the entire original theorem F in the frozen candidate, with every fixed real $q>4$, every $α\in(0,1/2)$, all-edge independent Pareto resistances, the original-degree clock including loop darts, and convergence through every positive integer map size. No restricted class, extra moment, conditioning event, or subsequence is needed. There is no blocking mathematical objection. The reconstructions below supply the details behind this verdict; the finite computations do not establish it.

This is an independent **proof** review, not a contribution, novelty, publication, or formalization verdict. The campaign remains at its supplied count 4/10 pending parent integration and the separate gates. No upstream truth is re-audited: the pinned OpenAI source is stipulated true. Candidate author: Myeongjin Kang, no affiliation. Original review prose is CC BY 4.0 and original review code MIT; third-party inputs retain their rights.

## 1. Frozen object, authentication, and audit boundaries

Review date: 2026-10-16. The audited object is

`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r7/`.

Every write in this review stayed in the assigned `fk-frechet-proof-r1/` directory. The directory did not exist initially and was created for the review. No candidate file was edited. No nested agent, staging, commit, shared-index edit, manuscript, Lean file, external message, upload, or publication was produced.

The external root of trust and key identities are:

| Object | Bytes | SHA256 |
| --- | ---: | --- |
| `seal.json` | 501 | `80f72efab2af1c25bb440a49fcaacd5410601d328b83c0f59055be65958ae7bc` |
| `inputs-manifest.json` | 7741 | `f077a3bb2cda73321d9edc9cbd84e32c76bb0187066236c35db2cc735b7a8ba8` |
| `outputs-manifest.json` | 2751 | `43890b3275d7f6bf1ddd7ee5bc06767e8143538cb65d06892f678ea4b3871857` |
| `candidate.md` | 24061 | `1b0e0608be24cb8f484f71643b1f488dace849509d4f21d442110bbb09750768` |
| `verify.py` | 4487 | `27e5e5dd5b84cdf241b2eb00097a212cc09cd17b65b27511b103167337fcbdd6` |
| `checks.py` | 11059 | `d968af3cc69f508b335e6a286c319a11b0629945537d9a1ea26373f79d08c5ef` |

The independently measured complete byte inventory is in `frozen-inventory.json`. The SHA256 root above, rather than the local convenience hash file, authenticated the package.

Before executing stored code, an independently written inline bootstrap checked the detached seal, both manifest hashes and byte counts, all 34 input and 18 output payload hashes and sizes, exact membership of the 56 files including four metadata files, and all 13 source Git blob SHA1 identities against the authenticated copied preprint tree. The bootstrap saved the independent complete inventory in `frozen-inventory.json`. Then the complete stored verifier and checker were inspected. Only afterward was the verifier replayed with Python `-B`; it reported byte-identical checker output, successful return, no stderr, and an unchanged package. A separate comparison with the independent inventory also found no changed byte after replay and the independent checks.

The exact original inventories and seal are retained as `candidate-inputs-manifest.json`, `candidate-outputs-manifest.json`, `candidate-seal.json`, and `candidate-seal.sha256`. The latter contains the original filename `seal.json`; it is a preserved convenience record, not a hash command for the renamed copy. `frozen-source-retrieval.json` retains all 13 pinned paths, URLs, Git blob hashes, SHA256 hashes, and sizes. `replay-authentication.json` records the replay result. These files preserve input/output membership without copying or redistributing the private source bodies.

Line references below are to the frozen `candidate.md`, not the user-message rendering. The candidate was read fully, lines 1–542; `original-scope.md`, both source contracts, `review-brief.md`, the verifier, checker, and author literature-screen were also read. The author's literature claims were not used as premises. Selected historical material in `strict-bv-parent/fresh-r7-brief.txt` was inspected as assignment history; it has no mathematical role here. No claim is made to having read its entire large appended history.

## 2. Exact theorem and source contract

For fixed $q>4$, the law on pairs $(M,A)$ of rooted spherical maps and edge subsets at size $n\ge1$ is proportional to

$$
q^{k_M(A)+(|A|-|V(M)|)/2}.
$$

Every map edge, including every loop and every parallel edge, receives an independent $R\ge1$ with $\mathbb P(R>r)=r^{-α}$ for $r\ge1$, independently of the map. Set $m(v)=\deg_M(v)$, counting a loop twice, and $M=2n$. The energy is the sum $\sum_{e=uv,\ u\ne v}R_e^{-1}(f(u)-f(v))^2$, with multiplicity. The variance is the unnormalized $m$-variance. Thus no factor $1/(2n)$ divides the variance or the energy. The generator is exactly the one in candidate lines 32–35, with the original degree in the denominator. In a one-vertex map, $\tau_n=0$.

The conclusion audited is

$$
\forall x>0:\quad
\lim_{n\to\infty}\mathbb P\{n^{-1/α}\tau_n\le x\}
=\exp\{-p_2\mathbb E|T|^α x^{-α}\}.
$$

Here $T$ is the *unconditioned* plane Galton–Watson tree for the exact law $p_{2j}=b_jv^j/\Phi(v)$, $p_{2j+1}=0$ at the pinned source parameter $v$; it is not a size-biased tree. All limits in $n$ are through all positive integers. There is no uniformity in $q\downarrow4$, α approaching an endpoint, or $x$, nor any such claim in F.

The immutable revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The common source manuscript path is

`preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/`.

`reviewer-source-contracts.json` records exact paths, pinned raw URLs, hashes, reading extents, and labels. Actual essential readings were:

| Source file | Lines read | Interface used |
| --- | --- | --- |
| `build/main.tex` | 1–167 | `eq:finite-law`, `eq:degree-measure`; root dart and loop conventions |
| `build/sections/blocks.tex` | 1–237 | block definition; `block:decomposition`, `block:one-edge`, `block:offspring`, `block:moments`, `block:finite-law` |
| `build/sections/trees.tex` | 1–150 | even law, all odd attainable sizes, `tree:conditioning`, lattice local limit |
| `build/sections/metric.tex` | 1–235 | `metric:measure` and exact pole/corner interpretation; CRT comparison not used to prove F |
| `build/sections/words.tex` | 1–115 | `word:parameters`, `word:weight` |
| `build/figures/corner-substitution.tex` | 1–45 | independent check of corner/pole multiplicities |

The upstream metadata and the relevant catalogue entry, lines 4873–4879 of the frozen `CONTENTS.md`, were checked for identification. No catalogue abstract replaces an actual source interface. The later path theorem was visible in the source inspection but is not a premise here. No companion proof, external primary-literature theorem, or external novelty screen is needed for the proof verdict; none is independently certified by it.

There is no source-law mismatch. Writing $t=\sqrt q$, `word:weight` defines

$$
a(M)=\sum_A t^{2k_M(A)+|A|-|V(M)|-1}.
$$

The decoration-summed finite-model weight is $t a(M)$. This map-independent factor disappears in the marginal at every $n$. `block:finite-law` asserts precisely that marginal, not an independent reconstruction of the decoration $A$; F needs only that marginal because its energy and added resistances do not use $A$.

For a link, the two subsets give contributions $t$ and $1$ to $a(B)$. For a loop they give $1$ and $t$. Thus each one-edge block has weight $1+t$, and the conditional chance of a link at offspring two is exactly $1/2$. The unconditional node chance is $\theta=p_2/2$. The nonempty blocks other than single loops are loopless, have at least two vertices, and have no separating vertex. This includes parallel-edge blocks and the one link. The source's representation has $N=2n+1$ nodes, independent block marks given offspring, and every such odd $N$ is attainable. Its critical law has $p_0p_2>0$, mean one, and finite positive variance. Those are the only offspring hypotheses used below.

## 3. Independent reconstruction of Lemma 3.1

Candidate lines 101–170, especially (3.4), (3.5), and the near-$N$ calculation, are valid.

Put $Y=\xi-1\in\{-1,1,3,\ldots\}$, $S_j=\sum_{i=1}^jY_i$, and $a_j(z)=\mathbb P(S_j=z)$. The span is *exactly two*: $-1$ and $1$ both occur, and all increments are odd. At compatible sites the source local limit has leading factor $2/(\sigma\sqrt{2\pi j})$. For odd tree sizes, the same factor occurs in numerator and denominator and cancels. In particular

$$
a_j(z)\le C(j+1)^{-1/2},\qquad
a_N(-1)\ge cN^{-1/2},
$$

for all relevant $j,z$ and odd $N$; finite initial sizes can be included by changing constants. With $a_0(0)=1$, this also includes an empty remainder. Fourier inversion on $[-\pi/2,\pi/2]$, with prefactor $1/\pi$, gives the upper bound from the quadratic characteristic-function modulus at zero and a strict modulus bound away from zero. No aperiodicity assumption on the full integer lattice is being made.

For a nonnegative marked-fringe toll $f$, set $h_s=\mathbb E[f(T);|T|=s]$. Start from the cyclic iid marked offspring list conditioned to sum to $-1$. Exactly one rotation is a tree word. A window of length $s$ that is itself a tree word has total $-1$, so the independent remainder must have total zero. Rotation preserves the sum of the fringe tolls over all starting positions. Therefore the exact normalized expectation is

$$
\frac1N\mathbb E F(T_N)
=\sum_{s\le N}h_s\frac{a_{N-s}(0)}{a_N(-1)},
\qquad F(t)=\sum_{u\in t}f(t_u).
$$

This reasoning also handles marks whose law depends on the node offspring: conditionally independent marks rotate with their offspring. Adding all edge resistances to the block mark is consequently legitimate.

The full-window term is $h_N/a_N(-1)$. Since $\mathbb P(|T|=N)=a_N(-1)/N$, this equals $N^{-1}\mathbb E[f(T_N)]$, exactly the normalized root term. Omitting it would make the identity false. It is not being silently replaced by an infinite-forest convention.

For fixed odd $s$, the ratio tends to one. For $s\le N/2$ it is bounded uniformly. For $s>N/2$, set $d_N=\sup_{s>N/2}s h_s\to0$. Then

$$
\sum_{N/2<s\le N}h_s\frac{a_{N-s}(0)}{a_N(-1)}
\le \frac{2Cd_N}{N}\sqrt N
\sum_{0\le j<N/2}(j+1)^{-1/2}\le C'd_N.
$$

This includes $s=N$ and proves the expectation limit using only the two stated conditions on $f$. Arbitrary integrability without the endpoint condition would not justify this step.

For a bounded toll restricted to fringe size at most $L$, each window function uses at most $L$ iid marked entries. Only $O(NL)$ ordered pairs of starting positions can overlap. Their contribution to the normalized second moment is $O(L/N)$, since the tolls are bounded even after conditioning. For disjoint tree windows of fixed odd sizes $a,b$, their totals are $-2$; hence the remaining increments must sum to $+1$. The factor is

$$
\frac{a_{N-a-b}(1)}{a_N(-1)}\longrightarrow1.
$$

It is lattice-compatible: $N-a-b$ is odd. Conditional offspring probabilities and mark integrals factor between the two windows before this single remainder factor. Finite summation over $a,b\le L$ gives vanishing variance. A size-tail cutoff is removed by the just-proved expectation limit; for a bounded toll its size-sliced means are $O(s^{-3/2})$, so the endpoint condition remains valid.

For the unbounded case, $f_H=f\mathbf1_{f>H}$ satisfies $h_s(f_H)\le h_s(f)$, and is integrable. At every fixed $H$, its normalized expected sum converges to $\mathbb E f_H$. Letting $H\to\infty$ proves (3.3); clipping $f$ at $H$ and Markov then proves the probability limit. One useful consequence used later is explicit: for any deterministic $H_n\to\infty$, the normalized expected sum of $f\mathbf1_{f>H_n}$ tends to zero. For each fixed $H$, it is eventually bounded by the sum with threshold $H$, after which (3.3) applies. No unjustified exchange of the two limits is required.

## 4. Independent reconstruction of Lemma 3.2

Candidate lines 172–233 are valid over the full range α in $(0,1/2)$ with only the second offspring moment.

The tree-size law gives $\pi_l=\mathbb P(|T|=l)\le C l^{-3/2}$, supported on odd $l$, with a positive asymptotic constant there. Thus $A_α=\mathbb E|T|^α\in(0,\infty)$; it diverges for α at least $1/2$. Independence of the children yields

$$
\mathbb E\left[\xi\sum_{i=1}^{\xi}|T_i|^α\right]
=\mathbb E\xi^2 A_α<\infty.
$$

The exact forest factor also follows from the skip-free cyclic argument. Explore a forest of $j$ ordered roots with $j$ waiting slots initially. A length-$t$ iid increment list with sum $-j$ codes such a forest precisely when $S_r>-j$ for $r<t$. Among its $t$ starting positions, counted with multiplicity even for a periodic list, exactly $j$ cyclic shifts have this property: they are the shifts selected by the $j$ descending-record levels in one periodically extended height interval of drop $j$. This is the same waiting-slot cycle argument as for one root. Cyclic invariance gives

$$
\mathbb P(|T_1|+\cdots+|T_j|=t)
=\frac jt\mathbb P(S_t=-j),\qquad t\ge j\ge1.
$$

Alternatively the generating function $F(z)=z\phi(F(z))$, where $\phi$ is the offspring generating function, gives $[z^t]F(z)^j=(j/t)[u^{t-j}]\phi(u)^t$; the coefficient on the right is exactly $\mathbb P(S_t=-j)$. These identities involve no moment assumption or analytic continuation.

For completeness the local forest estimate can be obtained without a positive exponential moment. For $0\le r\le r_0$, $Y\ge-1$ and $\mathbb EY=0$ imply

$$
\mathbb Ee^{-rY}\le1+C r^2\mathbb EY^2\le e^{C_0r^2}.
$$

For positive $Y$, use $e^{-u}-1+u\le u^2/2$; the negative part is bounded because $Y\ge-1$. Increasing $C_0$ if necessary, choose $r=a/(2C_0l)\le r_0$ whenever $0\le a\le l$. Chernoff gives

$$
\mathbb P(S_l\le-a)\le e^{-c a^2/l}.
$$

If $a>l$, the event is empty. This also deals with the slightly unequal halves for odd lengths in the next argument.

Split $S_t=U+V$ into independent sums of lengths $\lfloor t/2\rfloor$ and $\lceil t/2\rceil$. On $S_t=-j$, at least one of $U,V$ is at most $-j/2$. Summing over the value of that half and bounding the other half's point probabilities by $C/\sqrt t$ gives

$$
\mathbb P(S_t=-j)\le Ct^{-1/2}e^{-c j^2/t},
\quad1\le j\le t.
$$

The small values $t\le3$ are absorbed into constants. Impossible parity combinations contribute zero. Multiplying by the exact forest factor $j/t$ proves (3.7). Chernoff alone would lose the $t^{-1/2}$ prefactor and would not pay the later estimate; the candidate retains it correctly.

Let $h(t)=k\sum_i|t_i|^α$. Conditional on the root's even offspring $k\ge2$, exchangeability gives the exact convolution in (3.8). For selected child size $l\le s/2$, the residual forest size $s-1-l$ is comparable to $s$, and the forest estimate bounds this contribution by

$$
Cs^{-3/2}A_α
\sum_{k\ge2}k^3p_k e^{-c'(k-1)^2/s}.
$$

After multiplying by $s$, the sum to consider is

$$
\sum_{k\ge2}k^2p_k
\left[\frac{k}{\sqrt s}e^{-c'(k-1)^2/s}\right].
$$

The bracket is uniformly bounded for $k\ge2,s\ge1$, and tends to zero for each fixed $k$. Dominated convergence against $\sum k^2p_k<\infty$ proves this part is $o(s^{-1})$. The apparent $k^3p_k$ has **not** been summed without its damping factor. In particular the proof works for even critical offspring laws with tails proportional, for $k\ge4$, to $k^{-3}(\log k)^{-2}$ after suitably small tail mixing and adjusting $p_0,p_2$: their second moment is finite and third moment infinite.

For $l>s/2$, $l^α\pi_l\le Cs^{α-3/2}$. At each fixed $k$, summing the residual forest probabilities over its distinct possible sizes costs at most one. Hence this part is at most $C\mathbb E\xi^2s^{α-3/2}=o(s^{-1})$. No estimate uniform below α=$1/2$ is needed: for each fixed α<$1/2$, the exponent is strictly less than $-1$.

Finally if a nonnegative marked-fringe toll $f$ satisfies $\mathbb E[f\mid T]\le Ch(T)$, then both its unconditional mean and each size-sliced mean satisfy the same inequalities after taking expectation. This proves exactly the extension needed for the random electrical toll, including its uniform tail passage via Lemma 3.1. A pathwise domination by $h$ is not necessary.

## 5. Inverse-energy decomposition, weighted normalization, and exact mass

Candidate lines 239–301 correctly construct the entire inverse energy operator. This is stronger than a collection of cut lower bounds.

For a fixed connected map, work in $H=\{f:\sum m(v)f(v)=0\}$ with its $m$-inner product. The positive operator $A$ satisfies $\langle f,Af\rangle_m=\mathcal E(f)$; its inverse $K$ has norm $\tau$. There is no extra factor two: for the stated generator, each unoriented nonloop edge contributes precisely once to $\langle f,-Lf\rangle_m$. In the one-vertex case the space is zero dimensional and $K=0$.

For each nonloop block, ground its local potentials at the pole. Each component exterior to the block attaches at a single block vertex. Extend the local potential constantly into that component and then subtract its global $m$-mean. A different block's extension is constant across every edge of the first block, so cross energies vanish. Conversely the differences $f(x)-f(o_B)$ on each block reconstruct every global potential modulo constants, by summing over the articulation chain. Equivalently, the dimension identity is $\sum_B(|V(B)|-1)=|V|-1$, with loops contributing zero. Repeated attachments at the same articulation vertex cause no extra degree of freedom.

Let $F=\bigoplus_BF_B$ with its local-energy inner product and $J:F\to H$ the summed extension. It is an isomorphism preserving energy. Its adjoint is taken from $(H,\langle\ ,\ \rangle_m)$ to $(F,\mathcal E_F)$. Then

$$
\mathcal E(JJ^*g,f)=\mathcal E_F(J^*g,J^{-1}f)=\langle g,f\rangle_m,
$$

so $JJ^*=A^{-1}=\sum_BJ_BJ_B^*$, a positive sum. This calculation verifies that the adjoint is weighted; substituting an ordinary matrix transpose would be incorrect.

In an energy-orthonormal local basis $g_j$, the squared norm of evaluation at $x$ is $\sum_jg_j(x)^2=R_B(o_B,x)$. Therefore

$$
\operatorname{Tr}K_B=\sum_j\|J_Bg_j\|_m^2
\le\sum_v m(v)R_B(o_B,\operatorname{proj}_B(v)).
$$

The uncentered extension has zero value on the pole component. That component includes all the exterior root side; it is not to be assigned a nonzero resistance price.

Here is the exact conversion to the corner expression, including the subtle pole issue. A child subtree of $S$ nodes encodes an inserted map with $e=(S-1)/2$ edges. It supplies $2e=S-1$ inserted darts, including both darts of every inserted loop. The corner it occupies supplies one parent-block dart. Thus the corresponding corner allocation has exactly $S=2e+1$ units. For a nonpole vertex $x\in B$, all degree mass projecting to $x$ is the sum of these $S_i$ over the corners at $x$. Several corners can project to the same vertex, but each dart is assigned once. Any additional exterior mass is at the pole and has resistance price zero. Consequently (4.4) holds exactly as an upper bound. It is not a CRT or approximate-volume assertion.

For a link, only one corner is at the opposite endpoint. Removing that bridge gives a far-side set $A_e$ whose degree mass is exactly $s_e=|T_{i(e)}|=2e_{\mathrm{inside}}+1$. The boundary bridge dart contributes the final one. The root-side child attaches at the pole and is outside $A_e$. The local energy basis is $\sqrt{R_e}\mathbf1_{\mathrm{opposite}}$, and its centered global extension is $\sqrt{R_e}u_e$, with

$$
u_e=\mathbf1_{A_e}-s_e/M,\quad
\|u_e\|_m^2=t_e=s_e(1-s_e/M).
$$

Thus $K_e=R_eu_e\otimes_m u_e$, its sole nonzero eigenvalue and trace are $R_et_e$, and $0<t_e\le M/4$. These identities include loops in either side through $m$. Single-loop blocks have no potential space, contribute zero energy inverse, and still affect the degree mass of other blocks. Parallel edges remain separate terms of the local energy and belong to their cyclic block, never to the bridge sum.

## 6. Cyclic-block trace, with all-edge disorder and only the second moment

Candidate lines 303–362 pass. Any nonloop block other than a link is bridgeless. Indeed a bridge in a loopless connected graph with no separating vertex would force both its sides to have no other vertex, giving the single link. Thus two edge-disjoint paths connect pole to any distinct vertex. Choose the paths from the shape before revealing resistances; their length sum is at most the number $m_B$ of block edges. This includes a parallel-edge pair as paths of length one.

If $U$ is a sum of $l$ independent Pareto resistances, then for $t\ge1$

$$
\mathbb P(U>t)\le l\mathbb P(R>t)+t^{-1}l\mathbb E[R;R\le t]
\le C_α l t^{-α}.
$$

This is the event decomposition into a summand above $t$ or a truncated sum exceeding $t$. For the two paths, their sums $U_1,U_2$ are independent because they share no edges, whether or not they share vertices. Sending current down either path gives

$$
R_B(o,x)\le\min(U_1,U_2),\quad
\mathbb P(\min(U_1,U_2)>t)
\le\min(1,D t^{-2α}),\quad D=C_α^2l_1l_2.
$$

Enlarge $C_α$ so $D\ge1$. Integration below and above $D^{1/(2α)}$, together with $t<1$, gives

$$
\mathbb E R_B(o,x)^α\le C_α\sqrt{l_1l_2}\le C'_α m_B.
$$

The α moment of a single path sum would be infinite; the independent two-path gain is essential. There is no deterministic block-size cap or hidden moment on block shape.

For $Z_B=\sum_iS_iR_B(o,x_i)$, concavity and this estimate imply, conditionally on the full unmarked tree and the block shape,

$$
\mathbb E Z_B^α\le C_α k\sum_{i=1}^kS_i^α,
\qquad k=2m_B.
$$

Block shape and a vector of independent edge resistances form a valid node mark. The number of its edge coordinates is determined by $k$; this does not spoil independence between nodes. Set the toll to zero on leaves, links, and single loops. Lemmas 3.2 and 3.1 give bounded normalized expected total α toll and uniformly negligible expected toll tails on $T_N$.

Write $a_n=n^{1/α}$. For fixed δ>0, the chance of any $Z_B>δa_n$ is bounded by

$$
\frac1{δ^α n}\mathbb E\sum_B Z_B^α
\mathbf1_{Z_B^α>δ^α n}=o(1).
$$

The growing-threshold consequence of (3.3), established above, justifies this $o(1)$. For the truncated sum, deterministically

$$
\frac1{a_n}\sum_BZ_B\mathbf1_{Z_B\leδa_n}
\le\frac{δ^{1-α}}n\sum_BZ_B^α.
$$

Taking expectations costs $O(δ^{1-α})$. Markov, then $n\to\infty$, then $δ\downarrow0$, proves $\sum_BZ_B/a_n\to0$ in probability. The positive inverse decomposition converts this directly into a bound on the full cyclic-block operator norm. Dependence of fringe sizes and of tolls on shared descendant sizes is harmless: this argument uses expected sums and a union bound, not independence of those tolls. Every cyclic edge has been paid for through its block; no disorder was removed from those edges.

## 7. Exact bridge law and very large branches

Candidate lines 364–398 pass, with one nonblocking wording clarification recorded in Section 10 below.

The toll $f(T)=\mathbf1_{\mathrm{root\ link}}|T_{\mathrm{opposite}}|^α$ has mean $\theta A_α$ and is bounded by $h(T)$. Given offspring two, the link mark is independent of its two iid child trees, and the selected opposite child is a deterministic corner choice for a link. Hence Lemma 3.1, $N/n\to2$, and the exact bridge mass yield both expectation and probability convergence

$$
\frac1n\sum_{e\ \mathrm{bridge}}s_e^α
\longrightarrow2\theta A_α=p_2A_α=:K_0.
$$

For each fixed $L$, the same proof applied to the size-truncated toll gives the exact limiting tail mean

$$
\lim_{n\to\infty}\frac1n\mathbb E\sum_es_e^α\mathbf1_{s_e>L}
=2\theta\mathbb E[|T|^α;|T|>L]\longrightarrow0.
$$

On $s_e\le L$, $t_e^α=s_e^α(1-s_e/M)^α$ differs from $s_e^α$ by a factor tending uniformly to one. On the complement the difference is between zero and $s_e^α$, whose normalized expected sum has the just-established vanishing iterated tail. Therefore $n^{-1}\sum_et_e^α\to K_0$ in probability. The same reasoning also gives its expectation limit if needed.

This is exactly how very large far sides, including $s_e/M\to1$, are controlled. The proof never assumes $s_e=o(n)$ for every bridge, never treats an almost-total component as having centered mass $s_e$, and never conditions away a large branch.

Conditional on the map, the resistances on its bridges remain independent. Since $t_e\le n/2$ and $a_n/n\to\infty$, for each fixed $x>0$ and all sufficiently large $n$, all thresholds $a_nx/t_e\ge1$. Thus for $W_n=\max_eR_et_e$ (zero if empty),

$$
\mathbb P(W_n\le a_nx\mid M_n)
=\prod_e\left(1-\frac{t_e^α}{nx^α}\right).
$$

The largest subtracted term is deterministically $O_x(n^{α-1})=o(1)$, their sum converges to $K_0x^{-α}$, and their squared sum is bounded by their maximum times their sum, hence is $o_\mathbb P(1)$. The logarithmic expansion gives the conditional limit in probability. Boundedness permits taking expectation and yields the asserted Fréchet law for $W_n/a_n$, in particular its tightness. There is no factor-two loss: $N/n\to2$ cancels the $1/2$ chance that an offspring-two block is a link rather than a loop. No size bias enters $A_α$.

## 8. Spectral upper bound, overlap count, Gram comparison, and order of limits

Candidate lines 400–470 pass. The argument pays the spectral upper bound over the full original ensemble.

Fix ε>0, and call a bridge large when $w_e=R_et_e>εa_n$. Conditional Pareto tails, or the bound by one when its threshold is below the support, give

$$
\mathbb P(\exists\ \mathrm{large}\ e:s_e>L)
\le\frac{ε^{-α}}n\mathbb E\sum_es_e^α\mathbf1_{s_e>L}.
$$

The limit superior vanishes as $L\to\infty$ at each fixed ε. The count $J$ of all large bridges is tight because $\mathbb EJ\le Cε^{-α}$. There is no assertion of $J$ tight uniformly as $ε\downarrow0$.

Removing bridges gives a rooted tree of components, so their oriented far sides are laminar: two are nested or disjoint. A far side of degree mass $s\le L$ has exactly $(s-1)/2$ internal edges, including its loops. Thus it contains at most $L$ internal bridges. Summing over at most $n$ choices of an outer bridge bounds the number of nested pairs with both masses at most $L$ by $nL$. Each distinct pair being large requires two independent map-conditioned resistances exceeding $εa_n/L$. At fixed $ε,L$, those thresholds exceed one eventually. The union probability is at most

$$
nL\left(\frac{L^α}{ε^α n}\right)^2=O_{ε,L}(n^{-1}).
$$

Nested events need no independence from other pairs, only the two resistances within each pair. Together with the mass-tail bound, this proves that all large components are disjoint outside an event with an iterated small probability; it does not assert disjointness at a fixed finite $L$ without that exceptional event.

For disjoint components, the centered indicators have

$$
\langle u_e,u_f\rangle_m=-s_es_f/M,\qquad
\langle b_e,b_f\rangle_m
=-\frac{\sqrt{s_es_f}}{M\sqrt{(1-s_e/M)(1-s_f/M)}},
\quad b_e=u_e/\sqrt{t_e}.
$$

The Gram matrix has diagonal one and off-diagonal absolute values at most $L/(M-L)$ when both masses are at most $L<M$. The nonzero spectrum of the large-bridge sum is that of $D^{1/2}GD^{1/2}$. The row-sum bound for the symmetric $G-I$ gives

$$
\|D^{1/2}GD^{1/2}-D\|
\le W_n J L/(M-L).
$$

At fixed $ε,L$, $J$ and $W_n/a_n$ are tight, so this divided by $a_n$ tends to zero. The empty-large-set case is included by taking both norms and its maximum as zero. If $W_n\leεa_n$, replacing the empty maximum by $W_n$ is harmless for the desired *upper* bound, since the large operator is zero and is still at most $W_n$.

For any deterministic $t>0$, direct integration of the Pareto density gives, for $b\ge t$,

$$
\mathbb E[tR\mathbf1_{tR\le b}]
=\frac{α}{1-α}
\left(t^α b^{1-α}-t\right)
\le\frac{α}{1-α}t^α b^{1-α}.
$$

For $b<t$ the left side is zero, so the inequality still holds. With $b=εa_n$, $a_n^α=n$, and the bounded normalized expected sum of $s_e^α\ge t_e^α$, it follows that

$$
\limsup_n\mathbb E\left[a_n^{-1}\sum_{w_e\leεa_n}w_e\right]
\le Cε^{1-α}.
$$

These small bridge terms form a positive operator whose norm is at most its trace. Combined with Section 6, the entire inverse decomposes into the large-bridge operator plus a remainder whose normalized norm is small in the iterated limit.

For the lower bound, positivity gives $K\ge K_e$ in operator order for each bridge, whence $\tau_n=\|K\|\ge W_n$. A cut Rayleigh lower bound by itself would not establish this comparison's converse. The converse follows here from the inverse decomposition, the Gram estimate, and both trace payments.

More explicitly, put $T(L)=2\theta\mathbb E[|T|^α;|T|>L]$. For each η>0, the bounds imply, after harmless numerical changes in $C$,

$$
\limsup_{n\to\infty}
\mathbb P\{(\tau_n-W_n)/a_n>η\}
\le ε^{-α}T(L)+Cη^{-1}ε^{1-α}.
$$

For this inequality $n\to\infty$ is taken with $ε,L$ fixed; the pair-count error, Gram error, and cyclic error have already vanished. First send $L\to\infty$ at this fixed ε, then send $ε\downarrow0$. This proves $(\tau_n-W_n)/a_n\to0$ in probability. The Fréchet CDF is continuous at every $x>0$, so the extreme law transfers to τ. All source conditioning estimates held through all odd $N=2n+1$, and thus through every positive integer $n$. No subsequence extraction occurs in this proof.

## 9. Degeneracies and independent finite stress checks

The proof covers one-vertex maps: every block is a loop, $H=0$, and $K=W=\tau=0$. Their occurrence at finite $n$ does not need to be excluded. The positive limiting bridge intensity, established by the fringe theorem on the full ensemble, already implies their probability tends to zero.

At $n=1$, the map marginal is half one link and half one loop. On the link, $m=(1,1)$, the positive eigenvalue is $2/R$, and τ=$R/2$. On the loop, τ=$0$. This checks both the factor two and the convention at the smallest map size. F is an asymptotic assertion along all sizes, not an assertion of an exact finite-$n$ Fréchet law.

A bridge from a degree-one root to a vertex carrying $h$ loops has $s=2h+1$, total mass $2h+2$, and

$$
\tau=R\frac{2h+1}{2h+2}.
$$

Thus replacing $t$ by $s$ can fail by an arbitrarily large factor for a very large far-side branch. The candidate keeps the correct $t$ in the operator and extreme product and uses $s$ only for upper bounds and integrable tails. A two-vertex map with two parallel edges has harmonic effective resistance $(R_1^{-1}+R_2^{-1})^{-1}$, not either bridge resistance; the candidate treats it as a cyclic block.

The review's `independent_checks.py` does not import candidate code. It solves grounded Kirchhoff equations from zero-total current injections, assembles separate local block responses using graph-derived projections, and compares all zero-total basis responses exactly. Its nine-vertex graph contains a planar $K_4$, a theta block, nested bridges, three parallel edges, and loops at root and other articulation vertices. Both original degrees and independent nonuniform masses were checked: 16 full basis responses, with exact residual current conservation. It also checks the one-vertex case, parallel-edge harmonic resistance, and the explicit large-branch eigenvalue with $h=0,1,17,10^{12}$. The receipt is `independent-checks-receipt.json`; all checks passed.

These checks exercise graph equations and degeneracies independently of the candidate formulas. They do not establish the conditioning bounds, limit exchanges, or spectral asymptotics. Those are established by the mathematical arguments in Sections 3–8 of this review. The author's checker likewise remains finite support only; its simple negative controls are not promoted to asymptotic evidence.

## 10. Objections, precision notes, and disposition

**Blocking objections: none.** No mathematical repair or scope change is required for the proof verdict.

Two minor presentation clarifications are advisable when the parent later integrates the candidate; they do not change its proof or assumptions:

1. **Low severity, candidate lines 376–377, following (6.1).** “The same statement holds with” the indicator should explicitly give the limiting constant $2\theta\mathbb E[|T|^α;|T|>L]$, rather than leave “same” open to being read as the unchanged constant $K_0$. The following clause already says that limiting expectation tends to zero. Section 7 above reconstructs the intended exact statement and verifies it.
2. **Low severity, candidate lines 354–358, proof of (5.4).** “On the complement, the expected sum” is best displayed as the unconditional expected *truncated* sum $\mathbb E\sum_BZ_B\mathbf1_{Z_B\leδa_n}/a_n$. A conditional expectation given the no-exceedance event need not obey the displayed bound without dividing by the event's probability. The needed unconditional bound is exactly the deterministic truncation inequality in Section 6 above and proves the stated result. The existing argument naturally reads as this event-restricted expectation; no mathematical gap remains.

Neither note requires an author response to establish F. No proposed repair has been substituted for the frozen object, and the candidate remains unchanged. The review has independently reconstructed the delicate operations rather than accepting the checker or the parent assessment: the span-two root-inclusive fringe identity and near-$N$ payment; finite-variance negative local forest estimate; conditional-mark toll tails; weighted inverse-energy decomposition and exact loop-inclusive corner mass; arbitrary cyclic-block trace payment; the precise bridge intensity; overlap counting and Gram comparison; and the three-limit spectral upper bound.

**Final gate result: PASS for the entire original theorem F.** Contribution substantiality, novelty/priority, publication readiness, and Lean support remain separate, unreviewed gates. No result is counted or released by this report.
