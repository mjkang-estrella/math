# F002 — Edge and genus budgets for ordinary clique-free coloring

Status: **proved downstream corollary; independent review accepted after attribution and clarity corrections**. Assumes upstream family 184. No literature-priority or matching-sharpness claim.

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
2. [Ajtai–Komlós–Szemerédi (1980), *A note on Ramsey numbers*](https://doi.org/10.1016/0097-3165(80)90030-8) proves the following classical upper bound for every fixed r≥3. The pinned family-170 files below are in-repository restatements, not new inputs: (R(r,t)\le A_rt^{r-1}/(\log t)^{r-2}). For (r=4,5), the actual pinned family-170 manuscript *The sharp logarithmic exponent of r(5,t)*, `build/upper-bound.tex`, **`thm:upper` and its proof** (the proof explicitly establishes the (r=4) estimate first), supplies this. [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Sharp-Logarithmic-Exponent-of-r-5-t-September-24-2026/build/upper-bound.tex).
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
Split vertices into (L=\{v:\deg_G(v)\le D\}) and (H=V(G)\setminus L). The induced graph on (L) has maximum degree at most (D), and let Δ′ be its actual maximum degree. If Δ′<Δ_r, greedy coloring uses at most Δ_r colors. Otherwise the upstream theorem and monotonicity of x/log x for x≥3 give
\(\chi(G[L])=O_r(1+D/\log D)\).
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
Thus ((k-7)v(J)\le6g-12\le6g). Since (k\ge9), (v(J)\le3g), and (e(J)\le12g). Applying (C1) to (J) proves (C3). The inverted genus requirement uses g≥e(J)/12≥k(k−1)/24 to obtain log(g+2)≥c log k. This also handles a noncellular original embedding: passing to a cellular embedding of the subgraph does not increase the required genus.

### Novelty and usefulness

This is a routine Gimbel–Thomassen-type transfer of a maximum-degree theorem to edge and genus parameters. The useful gain is removal of an iterated logarithm, rather than a new decomposition method. It removes a logarithmic-iterated loss from the same derivation using Molloy's older degree bound: inserting (D\log\log D/\log D) instead gives an extra factor ((\log\log m)^q) in (C1), and therefore only the weaker edge requirement (\Omega_r(k^{1/q}\log^2 k/\log\log k)). [Molloy, primary manuscript, abstract and main results](https://arxiv.org/abs/1701.09133).

The analogous triangle-free edge/genus bounds are classical, so **do not market (r=3) as new**: [Gimbel–Thomassen, *Coloring triangle-free graphs with fixed size*, publisher DOI](https://doi.org/10.1016/S0012-365X(00)00087-X). The manuscript URL did not resolve through the browsing service; this comparison is also documented in [Harris's primary paper](https://arxiv.org/abs/1604.00438). The classical Ramsey reference is [Ajtai–Komlós–Szemerédi, *A note on Ramsey numbers*](https://doi.org/10.1016/0097-3165(80)90030-8).

Checked the actual upstream introduction/history and companion independence/Ramsey papers for these conclusions; no edge/genus statement was found. Targeted literature searches for clique-free edge/genus coloring did not locate exactly (C1)–(C3), but a search is not a novelty proof. **Recommended label: proved downstream corollary; plausible literature improvement, pending specialist review.** No matching lower bound, sharpness claim, constructive polynomial algorithm, list-coloring version, or DP-coloring version is asserted. The Ramsey independent-set removal proof is existential.

### Improvement and unresolved priority

The same classical Ramsey bound yields these minimum-edge requirements:

| Degree input | Lower bound for a k-chromatic K_r-free graph |
|---|---|
| Critical-subgraph argument alone | c_r k^(1/q) log k |
| Older Johansson/Molloy degree bound | c_r k^(1/q) log²k / log log k |
| Assumed upstream Δ/log Δ bound | c_r k^(1/q) log²k |

Thus the gain over the older-degree-bound derivation is one factor of
log log k. A prior conditional version assuming the Alon–Krivelevich–Sudakov
coloring conjecture may exist; this search does not establish absence.
The Gimbel–Thomassen full text could not be retrieved, while Harris's
abstract concerns triangle-count bounds. We therefore make no claim of
an exhaustive historical comparison or first formulation.

The conclusion is ordinary coloring. The Ramsey removal step supplies no
list/DP coloring bound at this strength. No efficient coloring algorithm,
uniform-in-r estimate, or matching construction is asserted.

### Validation

[Independent review](../reviews/graph-r1.md) verified every exponent and
logarithm, the small-degree case, critical-subgraph reduction and source
statements. All six requested changes are incorporated (the optional F-free
extension is not claimed). The parent independently re-derived the balance
p(1−q)=q and the genus bound e(J)≤12g.

`python openai-proof-research/experiments/complexity.py` passed exact rational
exponent checks for r=4,…,10. Its separate matrix-update checks are exploratory
and are not evidence for this graph theorem. No proof-assistant verification
is claimed.
