# r128 analytic screens and feasibility calculations

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Runner: Factory Droid, Opus 5.5 (high). Status: PREFREEZE. No scope was frozen at any time, so every calculation below is preselection feasibility work, not a candidate proof.

Pinned inputs are stipulated true at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The deductions written out below were checked by the author only. They are not independent correctness or contribution verdicts.

## 0. How the T372L127 lesson was applied

The required files were read in full before any family was chosen: `discovery-analytic-r127-parent/contribution-r1-adoption.json`, `t372l127-contribution-r1/public/generic-reduction.md` and `.../literature-comparison.md`. Their operative lesson is this. If a stability or rate version of a qualitative source theorem is obtained by quantifying each source step with classical estimates, it is TECHNICAL by calibration with i256 and T372L127.

Each screen below therefore asked two questions. (1) Is the proposed statement just a quantification of the source, or a composition of source steps? (2) What is the strongest generic reduction from actual source, companion, history and classical operations, and does it close the full statement? A screen could only become a freeze if (2) failed at a definite operation that I could also close. That never happened. Each screen ended either with a full compatible reduction (routine) or with a central step that I could not build (open).

Sources 372 (Lame), 082, 092, 101, 104, 111, 152, 174, 188, 197, 224, 228, 242, 253, 273, 277, 278, 290, 298, 300, 333, 334, 369 and 371 were not touched.

## S1. Source 331: is the diamond distortion lower bound sharp?

Source statement (actual `introduction.tex` and `diamonds.tex` of the reflexive tree-space manuscript, read in full). The space is X = J*. Here J is the completion of finitely supported functions on the forest of height-h trees T_h = N^{<=h}, under the segment norm rho(u) = sup over disjoint segments of (sum u(S_i)^2)^{1/2}. Every distortion-D embedding of the depth-k countably branching diamond satisfies D^2 >= 1 + k/12. The proof combines a squared midpoint loss of eps^2/48 from `lem:lens` with level-by-level summation L_m^2 <= L_{m+1}^2 - 1/12.

Question screened: is the order sqrt(k) sharp in this space?

Strongest generic reduction. An infinite antichain gives an isometric copy of l_2 inside X (actual identity (eq:antichain-isometry) in `forest.tex`). Any Hilbert-space embedding of D_k^omega therefore transfers isometrically. An upper bound O(sqrt k) would follow from a Hilbert embedding with that distortion. The natural candidate gives each refinement of each edge a fresh orthonormal offset of relative size about k^{-1/2}. The per-level stretch is then (1 + 4/k)^{1/2}, so the product over k levels stays bounded, and middle vertices are separated at relative size about k^{-1/2}. I did not check every vertex pair of this candidate, so the Hilbert upper bound is not verified here.

Disposition. Even if the Hilbert bound is verified, sharpness comes from a classical l_2 embedding placed in an isometric l_2 subspace. It does not interact with the source's AMUC, gate or cone machinery. It is not a new integrated operation, and the history archive I88 already treats the finite binary diamond strengthening as closed by Johnson–Schechtman. No freeze.

## S2. Source 090: are minimizers unique among periodic configurations?

Source statement (actual `01-uniform-gaussian-theorem.tex`, `06-...`, `07-...`, read in full). For every smooth completely monotone g and every locally finite configuration of centered disk density one, E_g(C) >= E_g(A). The source states explicitly that "it identifies the minimum value, not all minimizers", and that the torus corollary "asserts neither uniqueness nor exclusion of defects".

Question screened: if C is periodic with density one and E_g(C) = E_g(A) < infinity for a nonzero completely monotone g, must C be an isometric image of A?

Strongest generic reduction.
1. For periodic C, write E_g(C) as an integral of E_{G_alpha}(C) against the Bernstein measure. Each Gaussian inequality holds, so equality forces Gaussian equality for mu-almost every alpha.
2. In the periodic linear-programming chain at such an alpha, equality forces every nonzero difference vector into the zero set of G_alpha - f_alpha.
3. Suppose that zero set misses the open disk of radius lambda_1 (lambda_1^2 = 2/sqrt3 is the minimal squared norm of A). Then C is a periodic packing with minimal distance lambda_1 at density one. This is the Thue density. The classical periodic Delaunay argument then applies: each Delaunay triangle has area at least (sqrt3/4) lambda_1^2, and the average is exactly that. So every triangle is equilateral and C is triangular.

The remaining input is strict positivity of G_alpha - f_alpha below the first node, together with strictness at the origin for one alpha in the support. These are sign facts about the source and atomic-companion certificates. History I134 already records "strict deleted-jet margins" from the atomic companion. I did not read those certificate sections, and I did not verify this strictness here.

Disposition. Uniqueness is the classical packing equality case composed with source sign margins. History I134 and I137 also chose not to select it ("not uniqueness of all minimizers"). No freeze.

## S3. Source 090: a sharp auxiliary function for each potential (Cohn–Kumar quantifier)

The source says explicitly: "Integrating the resulting energy inequalities does not construct a sharp auxiliary for each mixed potential in the class required by Cohn and Kumar's conjecture. That stronger per-potential quantifier is not claimed here." Section 6 also states that "no measurable choice of the functions f_alpha will be needed". Alias searches for `per-potential`, `sharp auxiliary` and `Conjecture 9.4` found only source and companion bodies plus one external I134 download. They found no authored history note. These are navigation results, not a clearance.

Notation. A is the covolume-one triangular lattice, G_alpha(x) = exp(-pi alpha |x|^2), and S(alpha) = sum over a in A\{0} of G_alpha(a). f_alpha is the source pair from `lem:gaussian-duality`: f_alpha <= G_alpha, f_alpha^ >= 0, f_alpha = G_alpha on A\{0}, f_alpha^ = 0 on A*\{0}, and f_alpha^(0) - f_alpha(0) = S(alpha).

### S3.1 Elementary bounds (author deductions, checked)

(B1) f_alpha^ is nonnegative and integrable. Hence f_alpha(0) = integral of f_alpha^ >= 0, and |f_alpha(x)| <= f_alpha(0) for every x.

(B2) The positive part satisfies f_alpha^+ <= G_alpha. Hence f_alpha^(0) = integral of f_alpha <= integral of f_alpha^+ <= 1/alpha. Consequently S(alpha) <= f_alpha^(0) <= 1/alpha, and 0 <= f_alpha(0) <= min{1, 1/alpha - S(alpha)}.

(B3) The L1 norms satisfy ||f_alpha||_1 = 2 int f^+ - int f <= 2/alpha, and ||f_alpha^||_1 = f_alpha(0) <= min{1, 1/alpha}.

(B4) Lower bounds. f_alpha(0) >= f_alpha(a_1) = exp(-2 pi alpha/sqrt3). Poisson summation over the sublattice mA (m >= 2) gives sum over mA of f_alpha = m^{-2} sum over A*/m of f_alpha^ >= m^{-2} f_alpha^(0). By the direct contacts, the left side equals f_alpha(0) + S(m^2 alpha). Hence (1 - m^{-2}) f_alpha(0) >= m^{-2} S(alpha) - S(m^2 alpha). With m = 2 and large alpha, f_alpha(0) >= S(alpha)/3 - O(S(4 alpha)).

(B5) Mass heuristic, not a proof. Since f <= min(G_alpha, f(0)) and the disk where G_alpha >= f(0) has area about pi lambda_1^2 = 2 pi/sqrt3 as alpha -> infinity, the identity int f = f(0) + S forces f(0) >= (1 + o(1)) S/(2 pi/sqrt3 - 1).

### S3.2 Integrable potentials: a full compatible reduction (routine)

Claim, as a screen and not a nominee. Let g be completely monotone on (0, infinity) with integral of g over (0, infinity) finite. Then there is a radial continuous f_g with f_g and f_g^ in L1, such that f_g(x) <= g(|x|^2) for x != 0, f_g^ >= 0, f_g = g(|.|^2) on A\{0}, f_g^ = 0 on A*\{0}, and f_g^(0) - f_g(0) = E_g(A) < infinity.

Route.
- Integrability forces g(infinity) = 0. The classical Bernstein theorem then gives g(t) = integral of exp(-pi alpha t) d mu(alpha) for a positive Borel mu on (0, infinity). The integral of alpha^{-1} d mu equals the integral of g(|x|^2) over R^2, which is pi times the integral of g, so it is finite.
- Let E be the space of continuous f with f and f^ in L1, normed by ||f||_1 + ||f^||_1. It is a separable Banach space, and point evaluations are continuous on it. The set {(alpha, f): f satisfies the alpha-constraints} is closed in (0, infinity) x E, and its sections are nonempty by the source. Jankov–von Neumann uniformization gives a universally measurable selection alpha -> f_alpha. Its E-norm is at most 2/alpha + min{1, 1/alpha} by (B3).
- So the Bochner integral f_g = integral of f_alpha d mu converges in E. Evaluation and the Fourier transform commute with it. Every constraint holds pointwise. Also f_g^(0) - f_g(0) = integral of S d mu = E_g(A) by Tonelli, and this is finite because S <= 1/alpha.
- The lower bound of `prop:density-lp` needs only f in L1, f^ in L1 and the L1 tail. So f_g also certifies the energy bound.

Disposition. Every step is the source pair plus positive-definite bounds, Bernstein, Jankov–von Neumann and Bochner/Fubini. This is a routine composition. Its output also lacks the polynomial decay of the Cohn–Kumar admissibility class, because (B1) gives no decay of the negative part. Not nominated.

### S3.3 Singular potentials: the exact missing operation

For g(t) = t^{-p} with p > 1 (the convergent Epstein range), d mu is proportional to alpha^{p-1} d alpha, so the integral of alpha^{-1} d mu diverges near infinity. Using f_g = integral of f_alpha d mu then requires the integral of f_alpha(0) d mu to be finite. In view of (B4) and (B5), the natural sufficient input is a family of sharp pairs with f_alpha(0) <= C S(alpha) for all large alpha. Then the integral of f_alpha(0) d mu is at most C E_g(A), and the S3.2 argument goes through. Nothing in (B1)–(B5) rules this out.

Feasibility of that input. G_alpha / S(alpha) tends to 1/6 on the minimal shell, to infinity inside it, and to 0 outside it. So a normalized limit f_alpha/S would need to be at most 0 beyond lambda_1 while equal to 1/6 on the minimal shell. That is impossible for a continuous limit. At finite alpha the sharp pair would need a radial cliff of width O(1/alpha) at |x| = lambda_1, with f^ >= 0 and all dual contacts kept. This is an asymptotic sign certificate of Cohn–Elkies type with a boundary layer. The source's large-alpha construction (normalized pair with k = pi(alpha/b - h)) was not read beyond Section 6. No such family was built here, and no obstruction was proved.

Disposition. OPEN at the central sign construction. No local, integrable-only or decay-weakened substitute is nominated. This is the clearest exact gap left by this round.

## S4. Source 262: higher dimensions by lifting

Source statement (actual matrix `introduction.tex` and `notes/history.tex`, read in full). The sharp one-dimensional matrix inequality holds for 1/2 < gamma < 3/2 with the scalar one-bound-state constant, uniformly in the matrix size. The history notes credit Laptev–Weidl lifting, the HLW operator-valued bounds, and Read–Schulz at gamma = 1.

Strongest generic reduction. The analyticr118 intake (grep-level read of the `operator_compactness` entry) already pays the passage to operator-valued potentials, using source constants that are uniform in rows and columns. Laptev–Weidl lifting then turns operator-valued one-dimensional constants into d-dimensional Lieb–Thirring bounds. That is a direct composition. Its only new content would be numerical constants, a parameter compiler. Older chains (r112/r114 rotating-channel and multibump) are also credited. No freeze.

## S5. Source 143: Liénard extensions

Source statement (actual quintic `introduction.tex` read in full; `application.tex` read through its opening reduction). For deg F <= 5 the classical system has at most two limit cycles. The proof fits quadratic profiles in u = x^2/2, where the even part of F is common to both half-planes, and transports the fitted slope and curvature.

Screen. Degree six breaks the common quadratic even part (a cubic term in u appears), and its exact maximum is open: De Maesschalck–Dumortier already give four cycles, as the source intro cites. That makes it a headline whose central invariant is unbuilt. A nonlinear restoring force x(1 + beta x^2) is exactly the frozen and still unresolved T143D45 question of arithmetic r45–r47. Its frozen-scope and checkpoint openings were read late in this round, before any freeze of mine, and are credited. No freeze.

## Navigation-only exclusions (history read at displayed extents)

- 087: r53 already records the nonsymmetric polar-product width question c_G >= 2 + 2/n as unresolved. Only the ABKS capacity lower bound is paid.
- 373 and 374: r112, r114 and r122 record N-marginal and Riesz nonattainment (r54 full scope) and varying-source Brenier extensions.
- 097: I134 records Steinitz online, colorful and direct-sum variants as spent.

None of these was reopened.
