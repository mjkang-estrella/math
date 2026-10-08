> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Complexity/combinatorics research lane

**Status (2026-10-08):** One recommended structural deduction, with an equivalent extremal formulation and a surface consequence; one useful but standard-framework algebraic consequence. All pinned upstream theorems are assumed true. Neither result is certified new to the literature. No upstream-proof audit was performed.

Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Read `AGENTS.md`, `sources/upstream.json`, the relevant catalogue and overview entries, and actual manuscripts. `sources/tree.json` reports `truncated: true` and contains 58,727 entries; it is **not** a complete path inventory. Missing manuscript paths were resolved through pinned GitHub directory/tree requests; manuscript bytes were fetched from pinned raw URLs into the authorized ignored `sources/cache/complexity/` directory.

## 1. Recommended: edge and genus budgets for ordinary clique-free coloring

### Statement

Fix an integer (r\ge4), put
\[
 p=\frac{r-2}{r-1},\qquad q=\frac{r-2}{2r-3}.
\]
There is (C_r>0) such that every finite simple undirected (K_r)-free graph with (m) edges satisfies
\[
 \chi(G)\le C_r\left[1+
 \frac{m^q}{(\log(m+2))^{2q}}\right]. \tag{C1}
\]
Consequently there are (c_r>0,k_r) such that every such graph with chromatic number (k\ge k_r) has
\[
 m\ge c_r k^{(2r-3)/(r-2)}(\log k)^2. \tag{C2}
\]
If (G) embeds in a surface of Euler genus (g), then
\[
 \chi(G)\le C'_r\left[1+
 \frac{g^q}{(\log(g+2))^{2q}}\right]. \tag{C3}
\]
In particular, high chromatic number requires Euler genus
(\Omega_r(k^{(2r-3)/(r-2)}\log^2 k)).

Examples of (C2): (K_4)-free graphs require (\Omega(k^{5/2}\log^2 k)) edges; (K_5)-free graphs require (\Omega(k^{7/3}\log^2 k)); (K_6)-free graphs require (\Omega(k^{9/4}\log^2 k)). Constants depend on fixed (r); no uniform-in-(r) claim is made.

### Exact dependencies

1. Family 184, *Correspondence coloring graphs with a forbidden clique*, `build/sections/introduction.tex`, **Theorem `thm:main`**: for fixed (r\ge4), sufficiently large maximum degree (D) implies (\chi_{\mathrm{DP}}(G)\le\lceil C_rD/\log D\rceil). We use only its ordinary-coloring consequence.
   [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Correspondence-Coloring-Graphs-with-a-Forbidden-Clique-October-5-2026/build/sections/introduction.tex).
2. Classical upper bound (R(r,t)\le A_rt^{r-1}/(\log t)^{r-2}). For (r=4,5), the actual pinned family-170 manuscript *The sharp logarithmic exponent of r(5,t)*, `build/upper-bound.tex`, **`thm:upper` and its proof** (the proof explicitly establishes the (r=4) estimate first), supplies this. [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Sharp-Logarithmic-Exponent-of-r-5-t-September-24-2026/build/upper-bound.tex).
   For (r\ge6), *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers*, `build/sections/00-introduction.tex`, **`intro:main`**, supplies the upper bound with a constant, without epsilon loss. [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/build/sections/00-introduction.tex).

**The new Ramsey lower bounds are not needed.** Attribution of the upper bound to classical work matters: this proposal is a consequence of the new degree-coloring theorem combined with an old Ramsey bound, not a consequence of the new sharp lower construction.

### Complete proof

First the Ramsey bound gives, for every sufficiently large (N), an independent set of size at least
\[
 a_rN^{1/(r-1)}(\log N)^p
\]
in every (N)-vertex (K_r)-free graph. Indeed take
(t=\lfloor a_rN^{1/(r-1)}(\log N)^p\rfloor); since
(\log t\sim\log N/(r-1)), choose (a_r) small enough that (R(r,t)\le N). Floors and finitely many small values are absorbed into constants.

Remove such an independent set repeatedly, assigning it one new color. In a dyadic phase where the residual order lies between (N/2^{j+1}) and (N/2^j), each removed set has size at least a constant times
((N/2^j)^{1/(r-1)}(\log(N/2^j))^p). Thus the number of colors in that phase is at most
(O_r((N/2^j)^p/(\log(N/2^j))^p)), plus a constant. Summing the phases gives
\[
 \chi(H)\le B_r[1+(|V(H)|/\log(|V(H)|+2))^p]. \tag{1}
\]
For precision, phases above (\sqrt N) have logarithms comparable to (\log N) and a geometric sum (O(N^p/(\log N)^p)); phases below (\sqrt N) cost (O(N^{p/2}+\log N)), which is smaller. The finite final phases cost a constant.

For large (m), let
\[
 D=\left\lceil m^q(\log m)^{1/(2r-3)}\right\rceil.
\]
Split vertices into (L=\{v:\deg_G(v)\le D\}) and (H=V(G)\setminus L). The induced graph on (L) has maximum degree at most (D), and the new upstream theorem, enlarged to cover smaller actual degrees, gives
\(chi(G[L])=O_r(1+D/\log D)\).
The degree sum gives (|H|\le2m/D). Apply (1) to (G[H]), and use disjoint ordinary-color palettes on (L,H). Both terms are
\[
 O_r(m^q(\log m)^{-2q}),
\]
since (p/(1+p)=q) and
(p(1+1/(2r-3))=2q). This proves (C1), including arbitrary isolated vertices and small (m) after enlarging (C_r).

For (C2), (C1) gives (m\ge c k^{1/q}(\log(m+2))^2) for large (k). Also every (k)-chromatic graph has a (k)-critical subgraph, of minimum degree at least (k-1) and at least (k) vertices; hence (m\ge k(k-1)/2). Therefore (\log(m+2)\ge c'\log k), yielding (C2).

For (C3), take a (k)-critical subgraph (J), where (k=\chi(G)). If (k\le8) there is nothing to prove. Otherwise (J) is connected and has minimum degree at least (k-1\ge8). For a simple graph embedded in Euler genus at most (g), Euler's inequality gives
\[
 e(J)\le3v(J)-6+3g,\qquad
 e(J)\ge (k-1)v(J)/2.
\]
Thus ((k-7)v(J)\le6g-12\le6g). Since (k\ge9), (v(J)\le3g), and (e(J)\le12g). Applying (C1) to (J) proves (C3). This also handles a noncellular original embedding: passing to a cellular embedding of the subgraph does not increase the required genus.

### Novelty and usefulness

This changes the controlling parameter from maximum degree to edge budget and surface topology through an optimized decomposition and a critical-subgraph reduction; it is not a restatement of the upstream theorem. It removes a logarithmic-iterated loss from the same derivation using Molloy's older degree bound: inserting (D\log\log D/\log D) instead gives an extra factor ((\log\log m)^q) in (C1), and therefore only the weaker edge requirement (\Omega_r(k^{1/q}\log^2 k/\log\log k)). [Molloy, primary manuscript, abstract and main results](https://arxiv.org/abs/1701.09133).

The analogous triangle-free edge/genus bounds are classical, so **do not market (r=3) as new**: [Gimbel–Thomassen, *Coloring triangle-free graphs with fixed size*, publisher DOI](https://doi.org/10.1016/S0012-365X(00)00087-X). The manuscript URL did not resolve through the browsing service; this comparison is also documented in [Harris's primary paper](https://arxiv.org/abs/1604.00438). The classical Ramsey reference is [Ajtai–Komlós–Szemerédi, *A note on Ramsey numbers*](https://doi.org/10.1016/0097-3165(80)90030-8).

Checked the actual upstream introduction/history and companion independence/Ramsey papers for these conclusions; no edge/genus statement was found. Targeted literature searches for clique-free edge/genus coloring did not locate exactly (C1)–(C3), but a search is not a novelty proof. **Recommended label: proved downstream corollary; plausible literature improvement, pending specialist review.** No matching lower bound, sharpness claim, constructive polynomial algorithm, list-coloring version, or DP-coloring version is asserted. The Ramsey independent-set removal proof is existential.

## 2. Secondary: quadratic-cost hub rewiring of exact graph resolvents

### Statement and source

There exists a fixed (a>0.465) such that, for every (\varepsilon>0), the following batch operation uses (O_\varepsilon(n^{2+\varepsilon})) arithmetic operations over (F=\mathbb Q(z)): given adjacency matrices (A,A') of two (n)-vertex simple graphs whose changed edges all have an endpoint in a supplied set (S) of size (h\le n^a), and given (R=(I-zA)^{-1}), compute (R'=(I-zA')^{-1}) and the determinant ratio
\(\det(I-zA')/\det(I-zA)\).
The same conclusion holds over every characteristic-zero field with supplied inverses and nonsingular updated matrix. Choose (a<2/3).

Source: family 107, *Complex Matrix Multiplication Below 2.258 and Rectangular Bounds*, `build/rectangular/08-comparison.tex`, **`cor:characteristic-zero-dual`**: every characteristic-zero field has dual exponent (>0.465). [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/build/rectangular/08-comparison.tex). This is a fixed-field arithmetic statement, with constants allowed to depend on the field and epsilon. One can choose a common (a) from the corollary's proof, which descends the same complex scheme to each characteristic-zero field.

### Complete proof

Let (P) be the (n\times h) matrix selecting (S), and let (D=A'-A). Because the complement-by-complement block of (D) is zero, put
\[
 B=P^TD,\quad C=(I-PP^T)DP,\quad
 U=[P\ C],\quad V^T=\begin{bmatrix}B\\P^T\end{bmatrix}.
\]
Then (D=PB+CP^T=UV^T), so the update has rank at most (2h), even if it changes (\Theta(nh)) edges. Construct the factors in (O(nh)) operations.

Write (M=I-zA) and (X=-zU). Define (T=I_{2h}+V^TRX). Compute (RX) by fast rectangular multiplication. The (n\times n) by (n\times2h) shape has the same arithmetic exponent as (n\times2h) by (2h\times n): cyclic symmetry of the matrix-multiplication tensor, obtainable by transposing a bilinear multiplication circuit. Factor-two padding changes constants, not exponents. By the dual bound this costs (O_\varepsilon(n^{2+\varepsilon})). Compute (V^TRX) by padding to the same rectangular shape. Invert (T) and compute its determinant in (O(h^3)) operations by ordinary elimination, including exact zero tests for pivots; (3a<2), so this cost is below quadratic. Since (M) and (M+XV^T=I-zA') are invertible over (\mathbb Q(z)), (T) is invertible.

Woodbury gives
\[
 R'=R-RX T^{-1}V^TR,
 \qquad \det(M+XV^T)/\det M=\det T.
\]
Compute (V^TR), ((RX)T^{-1}), and the final (n\times2h) by (2h\times n) product using the same padding/cyclic-symmetry bounds. Only a constant number of rectangular products occur. The identity follows by multiplying the proposed inverse by (M+XV^T), using (T=I+V^TRX); the determinant identity follows from block elimination of
\(\begin{bmatrix}M&X\\-V^T&I\end{bmatrix}\)
using either diagonal block. This proves the statement.

The entries of (R'), expanded formally at (z=0), encode all walk counts, since ((I-zA')^{-1}=\sum_{j\ge0}z^j(A')^j). The theorem updates this representation, not an explicit list of infinitely many coefficients.

### Models, novelty, gaps

This permits polynomially more hubs than the historical dual-exponent bound (0.321334): [Vassilevska Williams–Xu–Xu–Zhou, primary paper](https://arxiv.org/abs/2307.07970). The output has (n^2) field elements, so its arithmetic exponent is optimal for explicit inverse output. It is **not** a new Woodbury algorithm: low-rank inverse maintenance already uses this framework, e.g. [*Faster Dynamic Matrix Inverse for Faster LPs*](https://arxiv.org/abs/2004.07470). Classification: useful graph interpretation and improved batch range, new to this project; not a demonstrated new algorithmic theorem. Do not lead the final research portfolio with this result if framework substitutions are excluded.

There is no claimed word-RAM or bit bound: unit-cost arithmetic over rational functions hides polynomial degrees, coefficient sizes and representation costs. There is no numerical stability claim, finite-field transfer of the dual exponent, online per-edge guarantee, or cost-free initial inverse. The symbol (n^{2+o(1)}) is shorthand only for a family of algorithms for every fixed epsilon; an epsilon-uniform implementation is not supplied. The witness (a>0.465) is not quantified explicitly upstream.

## 3. Rejected alternatives and breadth

- **Sparse triangle exponent (18/13+\varepsilon)** from (\omega\le9/4), dense triangles/transitive closure (9/4+\varepsilon), and ordinary determinant/inversion: valid standard reductions or already stated upstream, not promoted as new theorems. The (9/4) source is complex-arithmetic only: [family 107, `build/paper.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/build/paper.tex). Do not silently infer an exact integer/Boolean bit algorithm or the same bound over every field.
- **A piecewise rectangular-exponent frontier** interpolating (w(0.465)=2), (w(0.709)<2.092), (w(1)\le2.25): correct over complex arithmetic, but routine convex interpolation. The rectangular companion already develops aspect-ratio comparisons, so this is not a strong independent proposal.
- **Extending (C1) to list or correspondence coloring** using separate palettes: rejected. Ordinary color palettes can be disjoint globally; arbitrary lists or edge matchings do not provide this. The Ramsey removal bound controls ordinary coloring only. Max-degree DP coloring alone does not repair that gap.
- **Degree/edge lower bounds for near-extremal Ramsey witnesses**: directly plugging family 170 into family 184 independence is useful bookkeeping but too close to a substitution to promote.
- **Exact matching/prescribed factors (120), perfect-matching FPRAS (113), switch-chain mixing (131), thin trees (174), cycle decomposition (181)** were screened from catalogue/overview for natural interactions. Only the actual cycle-decomposition manuscript was read beyond this screening: [family 181, `build/main.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-linear-cycle-and-edge-decomposition-of-every-graph-September-24-2026/build/main.tex). None supplies an immediate novel, model-correct exponent beyond known reduction frameworks. No deductions relying on unread manuscripts are asserted.
- A Max-Cut consequence of (C1) follows from a random balanced partition of color classes, but stronger specialized clique-free Max-Cut literature may dominate it; not promoted without a dedicated comparison.

## 4. Independent checks and next steps

`experiments/complexity.py` verifies the threshold exponents exactly with rational arithmetic and checks the hub factorization and Woodbury identity on 40 reproducible small graph rewiring instances modulo a prime. The finite-field checks validate algebraic identities only, **not** transfer of upstream runtime bounds. These checks are not proofs of asymptotic constants or literature novelty.

Open research work: locate all fixed-clique edge/genus chromatic bounds and compare logarithmic factors; ask a coloring specialist whether (C1)–(C3) are already explicitly recorded as conditional AKS corollaries; determine matching lower bounds; investigate a genuine list/DP extension without the invalid palette argument. For the hub result, a meaningful bit-complexity theorem would require a rational-function representation and coefficient-growth analysis. Neither gap affects the stated arithmetic or existential deductions.
