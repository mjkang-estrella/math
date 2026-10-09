# I38 — uniform stability of Gaussian propellers

**Disposition: complete candidate proof, awaiting fresh independent proof and significance reviews.** Conditional on the stipulated corpus, the candidate proves a quadratic deficit bound for arbitrary Gaussian partitions, with one positive constant independent of both ambient dimension and the number of cells. This report does not accept a finding, change the count of five, or claim worldwide priority. Two other genuinely distinct screens are rejected below: geometric Mahler stability is already supplied by a classical local remainder plus compactness; global matrix Lieb–Thirring stability to its exact equality class is false already for scalar two-bump sequences.

The proposed operation is the combination of (i) a compactification allowing arbitrarily many Gaussian scores, with a proof excluding infinite-support optimizers, and (ii) an estimate of order **three** for activating arbitrarily many extra scores near a planar three-score optimizer. That estimate pays the order-two loss in normalization uniformly in the number of extra labels. Neither a fixed-cell compactness argument nor an unproved uniform Hessian bound is used to produce the rate. The finite-dimensional triangle calculation and the final calibration transfer are elementary and are not individually proposed as contributions.

All OpenAI premises are at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The full operative brief, relevant historical briefs/reviews, searches, responses and checks are in `frontier/sources/i38_inequality_stability_discovery/`; runnable scripts are in the corresponding experiment directory. Writes are confined to the three assigned I38 paths.

## 1. Three screens and their exact scope

### 1.1 Geometric Mahler stability — rejected as technical

For a fixed integer n≥2, let K be any origin-symmetric convex body in R^n, normalized in John's position, B₂⊆K⊆√n B₂. Put

\[
 \Delta_M(K)=\frac{n!}{4^n}|K||K^\circ|-1,\qquad
 d_M(K)=\inf_{H\text{ Hanner}}(d_{BM}(K,H)-1).
\]

The infimum includes all invertible linear images; translations are not symmetries of the centered problem. The candidate screen was the global estimate Δ_M≥c_n d_M, with c_n>0 for every fixed n and no dimension-uniform assertion. At n=1 both quantities vanish. Degeneration in eccentricity is removed by the GL(n) quotient and John's normalization, not by an implicit bound on the original coordinates.

The pinned manuscript `The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026`, `build/sections/introduction.tex`, Theorem `thm:main`, gives the sharp bound and exactly the linear Hanner equality class. Jaegil Kim, *Minimal volume product near Hanner polytopes*, arXiv:1212.2544v1, Main theorem, already gives P(K)≥P(H)+c(n)d_M(K) whenever d_M is sufficiently small. The final proof explicitly combines the linear excess with O(d_M²) errors; it is not merely strict local minimality. The fixed-dimensional Banach–Mazur compactum, continuity, and the finite set of Hanner combinatorial types give a positive deficit away from that neighborhood. Since d_M is bounded there, they extend Kim's estimate globally. This is precisely the sort of paid local-remainder/compactness bridge that the I30 and I36 significance reviews reject as substantial.

The functional corollary in the pinned introduction is a different interface: its Fradelizi–Meyer implication takes auxiliary dimensions n+m to infinity. The text explicitly warns that this limit does not classify functional equality. Neither a dimension-uniform geometric c_n nor a functional distance-to-extremizers estimate follows from the screened argument. No functional theorem is claimed.

### 1.2 Matrix Lieb–Thirring stability — global optimizer-distance target refuted

Fix γ∈(1/2,3/2), p=γ+1/2, and a finite matrix size m. For Hermitian W≥0 on R normalize ∫tr(W^p)=1, and let

\[
 \Delta_{LT}(W)=1-C_\gamma^{-1}\operatorname{Tr}(-\partial_x^2-W)_-^\gamma,
 \qquad d_{LT}(W)=\inf_{E\in\mathcal E_{\gamma,m},\,\int\!\operatorname{tr}E^p=1}
           \|W-E\|_{L^p(S_p)}.
\]

Here C_γ is the pinned one-state constant and E_{γ,m} is its exact equality class: a constant-unitary conjugate of at most m scalar sech² profiles in orthogonal channels. The quotient includes constant unitary changes and translations; each equality profile has its own scale and center, with the total normalization imposed. The hoped-for screen was **any** modulus d_LT≤ω_γ(Δ_LT) tending to zero, uniformly in m; even allowing ω to depend on m does not repair it.

The pinned October 5 equality manuscript's `thm:main` gives that class; `act:quantitative-action` already retains ∫|A′−BA|² and a truncated quadratic algebraic defect with coefficient depending on γ and the largest binding energy, independent of the number of rows and columns and the smallest binding energy. Its `comp:tail-bounds` subsequently uses the fixed physical rank m. Repackaging these auxiliary defects is technical. They are not a global distance to a single equality potential.

Here is the actual obstruction, not just a failed sufficient estimate. Put r=(γ−1/2)^{-1} and w_a(x)=(r+1)a²sech²(ra x). The source proves that w_a has sole negative eigenvalue −a² and ∫w_a^p=a^{2γ}/C_γ. Choose a=(C_γ/2)^{1/(2γ)}. Then

\[
 W_L(x)=w_a(x-L)+w_a(x+L)
\]

has ∫W_L^p→1. Two truncated, translated ground states have disjoint supports and Rayleigh quotients −a²+o(1). The min–max principle gives at least two eigenvalues at most −a²+o(1). The source upper bound then sandwiches its full spectral moment at C_γ+o(1). Normalize exactly by \(\widetilde W_L(x)=t_L^2W_L(t_Lx)\), where \(t_L=(\int W_L^p)^{-1/(2\gamma)}\to1\). Both the spectral moment and the potential integral scale by \(t_L^{2\gamma}\), so the spectral-to-integral ratio is invariant under this dilation and the normalized deficit tends to zero.

Every normalized nonzero scalar equality potential is w_A(·−b), with the fixed A=C_γ^{1/(2γ)}. Given a large fixed R, at least one of the two intervals of radius R around ±L/t_L is distance tending to infinity from b, uniformly in b. The L^p mass of w_A(·−b) on that interval tends uniformly to zero, whereas the mass of \(\widetilde W_L\) tends to ∫_{−R}^R w_a^p. The reverse triangle inequality and then R→∞ prove

\[
 \liminf_{L\to\infty} d_{LT}(\widetilde W_L)\ge 2^{-1/p}>0.
\]

Thus the target fails with m=1. This classical splitting phenomenon is not nominated as a new finding. Frank–Gontier–Lewin, arXiv:2109.05984v2, Theorem 1 on bubble decomposition and its translation-separated construction supply the relevant prior framework. Their compactness regime γ>max{0,2−d/2} in d=1 lies above 3/2, outside this screen. A matrix profile theorem allowing spatially separated, independently oriented bubbles would be a materially different target; it is not proved here. The endpoints γ=1/2 and γ=3/2 have different equality structures and are excluded. No constant is claimed uniform as γ approaches them, as ranks grow, or as binding energies collide or vanish.

### 1.3 Gaussian propeller stability — selected

For every d≥2 and every finite k≥3, let A=(A₁,…,A_k) be a measurable partition of (R^d,γ_d), allowing empty cells. Define

\[
 B=\frac{3}{2\sqrt{2\pi}},\quad
 F(A)=\sum_i\left\|\int_{A_i}x\,d\gamma_d\right\|^2,\quad
 \Delta(A)=B^2-F(A).
\]

Let P_{d,k} be the partitions made of three 120-degree sectors in a two-dimensional linear subspace, extended by its orthogonal complement, and k−3 empty cells, with all orthogonal rotations and label permutations allowed. Define

\[
 d_P(A)=\inf_{P\in\mathcal P_{d,k}}\frac12\sum_{i=1}^k\gamma_d(A_i\triangle P_i).
\]

This is the probability of a label disagreement after optimal alignment. There is no translation quotient, prescribed cell mass, smoothness, connectedness, or lower bound on nonzero cell probabilities. Arbitrarily small cells and increasing k,d are allowed. The theorem below gives **one universal positive constant** in Δ≥c d_P². The exponent is sharp. The branches d=1 or k≤2 are outside its distance definition; their optimal first-moment value is at most 1/π, strictly below B² (the one-cell value is zero).

## 2. Exact source and prior-proof interfaces

Write G for `preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026`. Its entire relevant geometric proof was read: `build/main.tex` through the Gaussian-maxima corollary; `extremizers.tex`, `scalars.tex`, `geometry.tex`, `elimination.tex`, and `certificates.tex`. Raw URLs are recorded file by file in the pinned manifest. The operative interfaces are:

- `thm:main` and `ext:duality`: E max_i⟨v_i,g⟩≤B(Σ|v_i|²)^{1/2}; zero scores may be added. The finite-list bound depends only on the vectors' span, not the surrounding dimension.
- `ext:structure`: exact optimizers are score partitions; merging a pair changes F by 2⟨z_i,z_j⟩; minimal active lists have negative pairwise products and span dimension m−1. The proof is inherited from Khot–Naor, Lemma 3.3, not a new operation here.
- `sc:bounds` and the deletion/translation argument: exact optimality, not merely near-optimality, yields the probability charges. The numerical constants .884, .929, .415, .15 have strict margins.
- `geo:pair` and `geo:second-constraint`: the first-moment identities and a two-dimensional residual Gaussian density bound control a pair of competitors. Section 4 below extends this actual calculation to countably many labels; it does not assert that all of G's finite-simplex operations extend.
- `elim:section`: strict rational margins exclude a negative-pairwise, m≥5 exact optimizer even when C=B². Each occurrence of C>B² used in those estimates may be weakened to C≥B²: r_i≤2/3 remains valid, the scalar endpoint interval is included, the two-score estimate becomes non-strict, and all final contradiction margins remain strict.

For m≤4 the external input is Heilman–Jagannath–Naor (HJN), *Solution of the Propeller Conjecture in R³*, the freshly retrieved Princeton author PDF, Theorem 1.1 and Remark 1.4. The latter explicitly states uniqueness up to rotations, labels and null sets. The current arXiv record is v2 (2014), but that version omits Remark 1.4; the author PDF and arXiv PDF are separately retained and are not conflated. The strict exclusion in the author proof, especially equation (77), and its explicit uniqueness remark supply the equality interface; it is not a quantitative uniform-in-k statement. Their estimates and Khot–Naor's finite-list duality, merging and simplicial reduction are the strongest directly relevant earlier proof operations inspected. They do not contain a countably indexed optimizing-limit argument or a summable estimate for activating unboundedly many extra scores.

Heilman's three-candidate paper (current arXiv:2306.03312v3, separately compared with the freshly retrieved author PDF) is a stronger comparison than simply saying “noise stability is different.” Theorem 1.5 includes a three-set result, and equations (53), (65), Lemmas 3.3, 4.1 and the circular rearrangement proof retain quantitative penalties. Those penalties control radial **three-set** measure imbalance; the positive-correlation theorem fixes the three Gaussian masses, and its dimension reduction applies to maximizers. The author PDF and arXiv v3 have different displayed numerical coefficients, so only their common three-set scope is used here; neither is a premise of (P). Its scalar angular concavity and rearrangement operations already pay the finite-three-angle part of the present analysis. They do not bound an unbounded family of unused labels or exclude loss of trace into such labels. Heilman–Tarter, arXiv:2011.05583v2, has the same finite-m dimension-reduction limitation for this purpose. Heilman's hyperstable-set paper, arXiv:2209.11216v1, Theorem 1.7, also retains a hyperstability hypothesis and at most four cells. None is treated as absent merely because its title differs. No conclusion about all worldwide prior art follows.

The closest direct quantitative predecessor is Heilman, [*Euclidean Partitions Optimizing Noise Stability*](https://www.stevenheilman.org/~heilman/papers/SSC.pdf), EJP 19 (2014), Lemma 2.8. Its entire proof, including Lemmas 2.5–2.7 and the closing discussion, was compared. It proves d₂≤6Δ^{1/8} for arbitrary **three**-cell partitions, where d₂²=2d_P; thus d_P≤18Δ^{1/4}. Its operations are merging to exclude bad centroid pairs, transferring misassigned halfspace mass, and controlling the resulting triangle by approximate stationarity. They already pay for qualitative/quantitative three-cell rigidity; neither that fact nor merely improving a finite-dimensional remainder is the proposed contribution. The proof's sum over three pairwise errors and its triangle stationarity step do not control a family whose number of cells diverges. In [*Stable Gaussian Minimal Bubbles*](https://arxiv.org/abs/1901.03934), current v1, Theorem 1.6 and Example 1.7 use this same three-cell moment-deficit estimate as a penalty in a surface-area theorem. Its general-m problem fixes all masses, and its constants depend on m and the masses. The closing Lemma 13.1 concerns a second variation at an optimizer, not uniform neighborhood entry across changing support. Heilman's [2021 robust Borell paper](https://arxiv.org/abs/2108.04950), current v1, treats a single set and halfspaces; its theorem and mechanism discussion were inspected, not its full proof. These additional comparisons narrow the proposed missing operation to Sections 4–6.1, coupled to the sharp exponent obtained afterward. They do not justify a worldwide novelty assertion.

## 3. The candidate theorem and constants

**Theorem P.** Under G and its stated primary inputs, there is a numerical c_P>0 such that for every d≥2, every finite k≥3 and every measurable Gaussian partition A,

\[
                         \Delta(A)\ge c_P d_P(A)^2.                 \tag{P}
\]

In particular, all but three labels have total mass at most \(c_P^{-1/2}\sqrt\Delta\), and those three masses differ from 1/3 by at most the same quantity. These are consequences of (P), not separate findings. The exponent 1/2 in the distance bound cannot be increased, already in d=2,k=3.

The following definitions specify a constant without pretending to have computed the global gap. For a finite vector list v of total squared norm one, append zero scores, order its norms decreasingly and put

\[
 M(v)=\mathbb E\max(0,\langle v_1,g\rangle,\ldots),\quad e(v)=B-M(v).
\]

For its first three entries let μ=(v₁+v₂+v₃)/3, u_i=v_i−μ, τ²=Σ_{i>3}|v_i|², E=τ²+3|μ|², S²=Σ_{i≤3}|u_i|²=1−E, and let α≥β≥0 be the two singular values of the matrix with columns u₁,u₂,u₃. Zero singular values are allowed. Set

\[
 E_0=(B/1600)^2,\qquad
 \eta=\inf\{e(v): E\ge E_0\ \text{or}\ \beta\le1/(2\sqrt2)\},       \tag{3.1}
\]

where the infimum is over all finite lists in all finite dimensions, with ties in ordering arbitrary. Section 5 proves η>0. It is not an explicit decimal certified by a numerical search. Let

\[
 c_0=\frac{3}{128\sqrt{2\pi}},\qquad c_V=\min(c_0,\eta/4),\qquad
 c_P=\left[36\left(B^{-1}+(2c_V)^{-1}\right)\right]^{-1}.           \tag{3.2}
\]

All are universal and positive. The rate in (P) comes from the explicit local estimates below; qualitative compactness supplies only entry into their fixed neighborhood.

## 4. Equality with an unbounded number of scores

This section supplies the missing compactness interface. We use a separable real Hilbert space H and an isonormal Gaussian process X(h), so E X(h)X(h′)=⟨h,h′⟩. It is not necessary or correct to posit an H-valued standard Gaussian vector with identity covariance when H is infinite dimensional.

### 4.1 Extension of the finite inequality and existence of score cells

For a countable list with Σ|v_i|²<∞, the vector (X(v_i)) lies in ℓ² almost surely and in L²(ℓ²). Monotone convergence applied to the positive maxima of the first N scores, and the finite-list inequality with zero appended, give

\[
 \mathbb E\sup(0,X(v_1),X(v_2),\ldots)\le B\left(\sum_i|v_i|^2\right)^{1/2}.   \tag{4.1}
\]

Every measurable event A has a first-chaos moment z(A)∈H defined by ⟨z(A),h⟩=E[1_A X(h)]. The map from L² to H is a contraction. For any finite or countable partition (A_i), the finite-vector dual estimate with zero appended gives Σ|z(A_i)|²≤B²: test any finitely supported array of vectors and then take its ℓ² dual norm. This also covers partitions depending on infinitely many Gaussian coordinates.

Suppose Σ|v_i|²=1 and the left side of (4.1) equals B. Since X(v_i)→0 almost surely, any positive supremum is attained. Assign its smallest maximizing index, and let A₀ be the event all scores are nonpositive. Distinct nonzero vectors have null tie events; identical ones cause no problem with this initial tie rule. Let z_i=z(A_i). Then

\[
 B=\sum_i\langle v_i,z_i\rangle\le(\sum_i|z_i|^2)^{1/2}\le B.
\]

The pairing is integrable, by the L²(ℓ²) bound. Equality in Hilbert-space Cauchy–Schwarz gives z_i=Bv_i and z₀=0. For any nonzero v_j, on A₀ its Gaussian score is nonpositive and is strictly negative almost surely conditional on a positive-probability A₀. Consequently z₀=0 forces P(A₀)=0. A duplicate nonzero vector would leave one corresponding cell empty, contradicting z_i=Bv_i. Every nonzero vector therefore has a positive-probability cell and the winner is unique almost surely.

The moment series satisfies Σz_i=0 strongly: partial sums are the moments of the corresponding unions, whose indicators converge to 1 in L². Merging any two cells and using the extended partition inequality shows

\[
                         \langle z_i,z_j\rangle\le0\quad(i\ne j).           \tag{4.2}
\]

These steps prove all identities needed next, rather than assuming a finite-dimensional extremizer lemma in infinite dimension.

### 4.2 No infinite-support optimizer

Assume infinitely many z_i are nonzero. Choose three fixed indices with positive radii r_j=|z_j|/B, j=1,2,3, and write c=min_{j≤3}r_j²>0. Choose a different nonzero index i with t=|z_i|/B→0. Let

\[
 e_i=z_i/|z_i|,\quad T=X(e_i),\quad
 a_j=-\langle z_i,z_j\rangle/|z_i|^2\quad(j\ne i),\quad
 w_j=z_j/B+a_jt e_i,\quad Y_j=X(w_j).
\]

Equation (4.2) and the strong sum imply a_j≥0 and Σ_{j≠i}a_j=1. Thus a_j≤1. The Y_j are jointly Gaussian and independent of T; their covariances satisfy

\[
 H_{jk}=\langle z_j,z_k\rangle/B^2-a_ja_kt^2\le0\ (j\ne k),\qquad
 h_j=H_{jj}=r_j^2-a_j^2t^2.
\]

On the winning cell A_i, T≥0 and Y_j≤(1+a_j)tT. Its first moments give E[1_{A_i}T]=Bt and E[1_{A_i}Y_j]=0. For any pair j,k≠i with D_{jk}=√(h_jh_k−H_{jk}²)>0, put U=Y_j/((1+a_j)t), V=Y_k/((1+a_k)t). The pair is independent of T and has density at most t²(1+a_j)(1+a_k)/(2πD_{jk}). Therefore

\[
 Bt=\mathbb E1_{A_i}(T+U+V)
 \le\mathbb E1_{\{T\ge0,U\le T,V\le T\}}(T+U+V)_+.
\]

At T=s the unweighted integral of (s+u+v)_+ on u,v≤s is (3s)³/6. Using E T_+³=2/√(2π) gives precisely

\[
                  D_{jk}\le(3/\pi)t(1+a_j)(1+a_k).                \tag{4.3}
\]

If D_{jk}=0, (4.3) is automatic; no singular density is used. This is G's pair operation, with all needed countable-list hypotheses verified above.

For sufficiently small t, h₁,h₂,h₃≥c−t²>0. Set ρ_{jk}=H_{jk}/√(h_jh_k). Positive semidefiniteness and ρ_{jk}≤0 give Σ_{j<k≤3}ρ_{jk}²≤Σ|ρ_{jk}|≤3/2. Hence

\[
 \frac32(c-t^2)^2\le\sum_{j<k\le3}D_{jk}^2
 \le 10(3/\pi)^2t^2.                                           \tag{4.4}
\]

For the last bound, Σ_{j≤3}a_j≤1 implies Σ_{j<k≤3}(1+a_j)²(1+a_k)²≤88/9<10, by the same elementary expansion as G. Letting t→0 contradicts c>0. Thus every countable equality list has finite support. Notice that neither the existence of a smallest positive radius nor an infinite-dimensional Ehrhard translation direction was assumed.

### 4.3 Finite equality classification

For a finite equality partition, any nonzero active cell with moment zero would be contained in the zero-score event, already proved null. If some pair of its moments has zero inner product, merge it; the objective is unchanged and the active count decreases. Repeat until every pair has negative inner product. The source's Gram-Laplacian argument gives rank m−1. If m≥5, the equality-compatible scalar/determinant elimination in Section 2 gives a contradiction. If m≤4, Gaussian factorization puts the score partition in dimension at most three, and HJN's uniqueness makes it a propeller with precisely three cells.

There could not have been an earlier zero-product merge: the last merge before reaching three cells would start from an equality partition with four active cells, whose moments sum to zero and whose score partition therefore lives in dimension at most three. HJN uniqueness forbids four active cells. Thus the original finite equality partition itself has three cells. Their moments are the propeller moments. Since z_i=Bv_i, an equality vector list consists of a centered equilateral triple of norm 1/√3 and zero vectors, up to isometry and relabeling.

## 5. A uniform compactness lemma, with no inferred rate

Let v^(n) be finite lists of total squared norm one, ordered by decreasing norm, in arbitrarily large dimensions. Put Q^(n)_{ij}=⟨v_i^(n),v_j^(n)⟩ and pad with zeros. Then Q^(n)_{ii}≤1/i. A diagonal subsequence has an entrywise positive-semidefinite limit Q with tr Q≤1. It is a Gram matrix of a countable list in a separable Hilbert space.

The expected maxima converge, not just their finite-dimensional distributions. Indeed, for any a>0 and M≥1, the Gaussian Chernoff bound gives uniformly in n

\[
 \mathbb E\sup_{i>M}X(v_i^{(n)})_+
 \le a+\sum_{i>M}\frac{e^{-ia^2/2}}{ia}
 \le a+\frac{e^{-(M+1)a^2/2}}{(M+1)a(1-e^{-a^2/2})}.             \tag{5.1}
\]

The first inequality integrates the union bound for t≥a, using ∫_a^∞e^{−it²/2}dt≤e^{−ia²/2}/(ia). Taking a=√(4log(M+1)/(M+1)) makes the last expression tend to zero. For a fixed head, convergence of its covariance matrices implies convergence of its expected positive maximum: realize it by their continuous positive square roots acting on one finite Gaussian vector, and use Cauchy–Schwarz. The same tail bound applies to Q. This proves convergence of M.

If e(v^(n))→0, the limit has M=B. Equation (4.1) forces tr Q≥1, so tr Q=1: no squared-norm energy escapes into the tail. Section 4 says Q is the Gram matrix of an equilateral triple and zeros. The decreasing diagonal order puts the three nonzero vectors first. Consequently E(v^(n))→0 and β(v^(n))→1/√2. This contradicts membership in the closed complement in (3.1). Therefore η>0.

This is a **uniform** neighborhood-entry lemma despite unbounded k and d. It establishes no modulus by itself. In particular, no power law is being extracted from equality or compactness.

## 6. Local estimate with arbitrarily many extra labels

Let v be in the local region E<E₀, β>1/(2√2). Work in the two-dimensional span L of u₁,u₂,u₃, and let R=|g_L|. Since u₁+u₂+u₃=0, there is a linear map from a unit equilateral triple to these u_i whose singular values are √2α,√2β. An equilateral triple of norm 1/√3 has inradius 1/(2√3). Thus

\[
                \max_{i\le3}\langle u_i,g_L\rangle\ge hR,
                \qquad h=1/(4\sqrt3).                         \tag{6.1}
\]

### 6.1 Extra-score activation has order three

For j>3, the L-projection of v_j−μ has norm at most τ+|μ|≤2√E. The same bound holds for the externally appended zero score minus μ. Since E≤E₀, 2√E≤h/2. Put

\[
 Z=\left(\sum_{j>3}X(v_j^{\perp})^2\right)^{1/2}+|X(\mu^{\perp})|.
\]

This variable is independent of R. Comparing every extra score, including zero, to the three-score maximum and subtracting the common μ score gives pointwise

\[
 0\le\max(0,X(v_1),X(v_2),\ldots)-\max_{i\le3}X(v_i)
       \le (Z-hR/2)_+.                                       \tag{6.2}
\]

If G is any centered finite Gaussian vector with E|G|²=τ², then E|G|⁴≤3τ⁴, so E|G|³≤3^{3/4}τ³. This uses the covariance eigenvalues, not its rank. Also E|X(μ^⊥)|³≤2√(2/π)|μ|³. The scalar inequality (a+b)³≤4(a³+b³) consequently gives

\[
                            \mathbb EZ^3\le12 E^{3/2}.         \tag{6.3}
\]

The density of the independent planar radius is r e^{−r²/2}. For z≥0 and c=h/2,

\[
 \mathbb E_R(z-cR)_+\le\int_0^{z/c}(z-cr)r\,dr=z^3/(6c^2).
\]

Here 1/(6c²)=32. Integrating (6.2)–(6.3) proves

\[
              M(v)\le M_3(u)+384E^{3/2}\le M_3(u)+400E^{3/2}.  \tag{6.4}
\]

This is the summable estimate needed at the changing-support boundary. Summing separate one-label error bounds or applying a fixed-k Hessian theorem would not establish its uniformity. Correlations among extra scores are arbitrary; independence is used only between the plane and its orthogonal complement.

### 6.2 The exact three-score remainder

Let ℓ₁,ℓ₂,ℓ₃ be the side lengths of the centered triangle u. The planar Gaussian support-function formula gives

\[
                   M_3(u)=\frac{\ell_1+\ell_2+\ell_3}{2\sqrt{2\pi}}.         \tag{6.5}
\]

For completeness, the angular integral of the support function of a planar convex polygon is its perimeter: on each normal-angle interval integrate the supporting vertex's dot product with the unit direction and telescope the endpoint terms. Multiplication by E R/(2π)=1/(2√(2π)) gives (6.5). A common μ score has mean zero and does not change this expectation.

We have Σℓ_i²=3S² and ℓ_i≤√2S. Moreover, the three edge directions of a reference equilateral triangle, separated by 60 degrees modulo sign, give

\[
 \sum_{i<j}(\ell_i^2-\ell_j^2)^2=\frac92(\alpha^2-\beta^2)^2.              \tag{6.6}
\]

This identity follows by writing the squared lengths as S²+(α²−β²)cos(2θ_i−φ) and summing; no Hessian assumption is involved. Therefore

\[
 3S-\sum_i\ell_i
 =\frac{\sum_{i<j}(\ell_i-\ell_j)^2}{3S+\sum_i\ell_i}
 \ge\frac{3(\alpha^2-\beta^2)^2}{32S^3}.
\]

Since (α+β)²≥S² and S≤1, this implies

\[
 B S-M_3(u)\ge\frac{3}{64\sqrt{2\pi}}(\alpha-\beta)^2.                    \tag{6.7}
\]

Combining (6.4), (6.7), 1−√(1−E)≥E/2, and 400√E≤B/4 gives

\[
 e(v)\ge\frac B4E+\frac{3}{64\sqrt{2\pi}}(\alpha-\beta)^2.                \tag{6.8}
\]

Let T denote the set of arrays containing a unit equilateral triple and zeros, in the same ambient space and with arbitrary labels. Polar decomposition on the centered three-column matrix supplies such an array t, supported on the first three entries, with

\[
 \|v-t\|_{\ell^2}^2=2-\sqrt2(\alpha+\beta)
 \le 2E+\frac{(\alpha-\beta)^2}{S}
 \le2E+2(\alpha-\beta)^2.                                    \tag{6.9}
\]

To verify the middle bound, put d=(α−β)²/S² and use √2(α+β)/S=2√(1−d/2) and 1−√(1−x)≤x; also 1−S≤E. The local region has S≥1/2. Equations (6.8)–(6.9) prove e(v)≥c₀ dist(v,T)² with c₀ from (3.2).

Outside the local region, e(v)≥η and the distance between any two unit arrays is at most 2. Consequently, for lists in ambient dimension at least two with at least three labels (zero padding permitted), the all-list estimate is

\[
                         e(v)\ge c_V\operatorname{dist}(v,T)^2.           \tag{6.10}
\]

No dimension, rank, number of labels, or smallest cell mass appears in this bound.

## 7. Transfer to arbitrary measurable partitions and sharpness

Let z_i be the moments of A and assume F>0. Set v_i=z_i/√F. These vectors have total squared norm one, and assigning each point its actual label shows M(v)≥√F. Choose the aligned t in T furnished by (6.10); a minimum exists for this finite list. Its three score cones define a propeller P with the same labels. Since |v|=|t|=1,

\[
 \begin{split}
 J&=\mathbb E\big[\max_i X(t_i)-X(t_{A(g)})\big]
       =B-\sum_i\langle t_i,z_i\rangle\\
  &=B-\sqrt F+\frac{\sqrt F}{2}\|v-t\|^2
       \le\left(1+\frac B{2c_V}\right)(B-\sqrt F)
       \le\left(B^{-1}+(2c_V)^{-1}\right)\Delta.                \tag{7.1}
 \end{split}
\]

The **squared** vector distance in this identity is essential: a mere Lipschitz estimate would lose an unnecessary square root.

Let ε=P(A(g)≠P(g)) for this alignment, and let G(g) be the margin from the winning t score to the best score carrying a different label. Pairwise differences of the three active scores are N(0,1); an inactive score is zero. Thus, for 0<s≤1,

\[
 \Pr(G\le s)\le3\sqrt{2/\pi}\,s+6s^2\le9s.                  \tag{7.2}
\]

The first term covers the three pairwise hyperplane slabs. For the second, max t_i·g≥R/(2√3), and P(R≤2√3s)≤6s². If there are no inactive labels this additional bound is harmless. On a mismatch the calibration loss is at least G. Choose s=ε/18≤1; then J≥s(ε−9s)=ε²/36. Since d_P≤ε, (7.1) yields (P) with (3.2). If F=0, Δ=B² and d_P≤1; the same constant works since c_P≤B/36<B².

To test the exponent, in R² take consecutive sector openings 2π/3+t, 2π/3−t, 2π/3 for small positive t. Their first-moment formula gives exactly

\[
 \Delta=\frac{1-\cos t}{4\pi},\qquad d_P=\frac{t}{2\pi}.       \tag{7.3}
\]

For the distance, the three boundary shifts from a reference propeller are 0,t,0. Optimizing a common rotation minimizes |θ|+|t−θ|+|θ| at θ=0. For sufficiently small t, any better alignment would have to be close to one of the equivalent cyclic/reflected alignments; the same median calculation applies. Equivalently, the cell of opening 2π/3+t has excess mass t/(2π), a lower bound on every disagreement probability, and the unrotated alignment attains it. Therefore Δ/d_P²→π/2. No estimate d_P≤CΔ^a with a>1/2 can hold even with d,k fixed at 2,3.

## 8. Adversarial checks and decision limits

The following possible shortcuts were specifically avoided or tested.

1. **Fixed-k compactness:** its constant may depend on k. The trace compactification, the Gaussian tail estimate (5.1), and the infinite-support exclusion (4.4) are needed to justify a single η. Equality classification alone is not that argument.
2. **Deleting cells in a near-optimizer:** the source's identities for translated cone probabilities use exact stationarity. Applying them directly to a near-optimal arbitrary partition is unjustified. Our proof uses them only for exact finite equality limits; the countable argument needs only the two-score moment calculation.
3. **Tiny or numerous extra cells:** their scores may be arbitrarily correlated and their combined support may have large cardinality. Estimate (6.3) uses their summed covariance trace, and the two-dimensional radial integral in (6.4) supplies the additional power. There is no union bound over extra-label boundaries in (7.2).
4. **Rank collapse and translations:** the local proof explicitly requires β>1/(2√2); entry into that region is proved globally. The Gaussian origin is fixed. The common mean of the active three scores is retained in E and Z; it is not silently subtracted from every label without paying for the inactive labels.
5. **Noncommuting matrix wells:** the LT source auxiliary remainder is real and useful, but the scalar splitting example already destroys the screened target before any noncommutative question arises.
6. **Prior quantitative results:** Mahler's linear local remainder and the three-candidate angular/noise-stability remainders are credited. A primary proof that already combines a countable-label compactification with a uniform extra-score estimate would change the significance assessment. The present bounded search does not rule that out globally.

The exact diagnostics check the triangle Gram identity and remainder algebra, Gaussian fourth-moment trace algebra, residual coefficient expansion and constants, radial cubic integral, normalization bookkeeping, and the sharp-sector expansion. Additional deterministic floating quadrature explores 1, 4, 32 and 1,024 independent extra scores at tail energies from 10^{-3} to 10^{-8}; it is marked as non-certified. The activation divided by E^{3/2} remains bounded in these tests. The analytic proof handles arbitrary correlations; the diagnostic does not test all of them. None proves the universal analytic theorem, and no source numerical certificate is relabelled as a new independent computation.

The proof dependency graph is:

`G finite sharp inequality + finite equality-compatible elimination + HJN uniqueness`
→ `countable sharp inequality and equality moments`
→ `countable residual determinant exclusion`
→ `uniform compactness/neighborhood entry`;

`exact triangle geometry + Gaussian trace moment bound + planar radial integral`
→ `uniform local quadratic score deficit`;

both branches → `global score stability` → `squared-pairing calibration + three-boundary margin bound` → `(P)`.

The novel candidate is this full mechanism and uniform theorem, not its elementary pieces. Separate independent proof and significance decisions remain required. There is no acceptance/count change.

## 9. Evidence and reproduction

The evidence records distinguish full proof-operation reads from selected comparison passages, and mechanical full-corpus searches from semantic reading. The complete tree has 13,223 entries and 749 manuscripts; the old contents catalogue has 719. All 9,340 cached text files, totaling 141,349,121 bytes, were freshly SHA-256 and Git-blob checked against that complete tree and the retained corpus manifest. The corpus was reused read-only, not copied. `corpus-screen.json` retains the patterns and matching contexts. Prior-project screening and its exclusions are separately recorded: the initial scan covered 4,123 eligible files, and the final scan covered 4,124, with a full eligible-file hash inventory. These scans found no earlier candidate/review Markdown containing the three selected subject names; a name-based screen is not a semantic nonduplication proof.

`input-manifest.json` freezes the rules, pin, complete inventory, ledgers, brief and historical gate reviews. Mutable shared-ledger drift is reported separately from immutable source/review drift. `pinned-manifest.json` records 74 raw pinned URLs and Git/SHA identities across six manuscript folders; 13 full operative source files were read. `source-contracts.json` binds the relied-on theorem and internal-operation labels; `read-passages.json` identifies the actual ranges read. The main primary downloads have complete request/response metadata and saved bytes, including failures: a publisher's FGL PDF returned 403, an incorrectly guessed FGL v3 returned 404, then current metadata identified v2 and that PDF was retrieved successfully. These failed payloads are excluded as proof inputs. An initial broad web batch was exploratory and not retained; the subsequent six numbered query batches are retained in full and are the sealed search evidence. The sixth broad search returned substantial irrelevant engineering material; those hits were not used as mathematical evidence. No search-absence assertion is a proof of novelty.

`artifact-seal.json` binds the report and owned immutable artifacts, including the ignored local download/extraction caches. Its manifest and verifier are retained; the caches remain subject to the project ignore policy. The verifier requires those local caches and the stated read-only corpus; it does not silently fetch replacements for sealed bytes. The verifier does not rewrite the seal or any earlier dependency; its only generated output is in the I38 experiment directory. Run from the project root:

```sh
python -B frontier/experiments/i38_inequality_stability_discovery/diagnostics.py
python -B frontier/experiments/i38_inequality_stability_discovery/verify.py
```

Integrity PASS and exact finite diagnostics are evidence, not an independent mathematical audit or formal certification. Parent integration, independent reviews, any separate finding commit and publication remain outside this task.
