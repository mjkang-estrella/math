# r129 analytic screens and feasibility calculations

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Runner: Factory Droid, model Opus 5.5 (claude-opus-5-5), high. Status: PREFREEZE. No scope was frozen at any time. Every calculation below is preselection screening, not a candidate proof, and it carries no correctness or contribution verdict.

Pinned inputs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true, including their operative proof operations. The deductions below were checked by the author only.

## 0. Order of work

1. AGENTS.md and the full r129 brief. Then the r128 handoff required by the brief: `fresh-analytic-discovery-r128/REPORT.md`, `packet/public/report.md`, `screens.md`, `reading-limits.md`, and `discovery-analytic-r128-parent/intake.json`.
2. Optional focus (S3 of r128). Fresh acquisition of source090 (universal optimality of the triangular lattice) sections 01–07 and 09, and the atomic companion `main.tex`. Sections 02, 04 and 06 were read in full, and the parts of 01, 03 and 05 listed in reading-limits.md. The resolution in Section 1 below came from the source's Proposition `prop:exact-interpolation`.
3. Atomic companion introduction and energy section (lines 120–509), to check whether either source claims the per-potential auxiliary. Neither does.
4. Second family: source191 (Heilbronn). Fresh acquisition, introduction read in full, and lemma statements of sections 05, 07 and 08. I made a dimension-three feasibility calculation (Section 2.2 below).
5. Alias searches with no size cutoff (search-receipts.json). They found the arithmetic r56/r57 frozen archive T191V56 (three-dimensional Heilbronn), which I then read at the recorded extents. This was late, after my own Section 2.2 calculation and before any freeze of mine. No freeze followed.

## 1. S3 resolved: the per-potential sharp auxiliary closes by routine composition

### 1.1 What r128 left open

Both pinned sources explicitly leave the Cohn–Kumar per-potential quantifier unclaimed. Source090 `01-uniform-gaussian-theorem.tex` says: "Integrating the resulting energy inequalities does not construct a sharp auxiliary for each mixed potential ... That stronger per-potential quantifier is not claimed here." The atomic companion says: "Mixing the Gaussian energy inequalities does not by itself construct such an auxiliary for a general potential."

r128 reduced the singular case g(t) = t^{-p}, p > 1, to the integrability of f_alpha(0) against dmu ~ alpha^{p-1} dalpha at alpha -> infinity. It then asserted that one needs f_alpha(0) <= C S(alpha), and that this would require a new Cohn–Elkies-type boundary-layer sign certificate. That assertion is wrong in both parts. S(alpha) decays exponentially, so any bound f_alpha(0) = O(alpha^m S(alpha)) suffices. And the source construction already gives m = 1, uniformly, through its own coefficient bound. No new sign certificate is needed.

### 1.2 The paid source inputs

Notation from source090 `02-cardinal-fourier.tex`: b = sqrt3/2, h = 2/5, s = b|x|^2, T_k(s) = k^{-1} e^{-k(s-1)}. The minimal lattice shell is s = 1, that is |a|^2 = 1/b.

(P1) Lemma `lem:gaussian-duality` (06). For alpha >= 1, f_alpha = k e^{-k} f with k = pi(alpha/b - h) >= 2.36. Here f(x) = e^{-pi h s} H_1(s) and fhat(xi) = e^{-pi h s} H_2(s), with H_1 = p_{l_1} + K_{p_{l_2}} and H_2 = p_{l_2} + K_{p_{l_1}}, from Theorem `thm:normalized-pair`. For 0 < alpha < 1 and beta = 1/alpha, f_alpha = beta qhat_beta with q_beta = G_beta - f_beta. Equivalently f_alpha = G_alpha - beta fhat_beta and fhat_alpha = beta q_beta.

(P2) Proposition `prop:exact-interpolation` (04). For every real k >= 2.36 there is a unique pair of lists l_1, l_2 in the unweighted l^1 coefficient space, with extras e_i = E_i q(k), and the pair satisfies **||l_1||_1 + ||l_2||_1 < 5**. The lists solve L(a_1, a_2) = (J T_k + S_e e_2, S_e e_1), where L = [[I, -S], [-S, I]] is a fixed bounded operator, independent of k, with bounded inverse. Section 05 opens with "take the exact lists l_1, l_2 from Proposition prop:exact-interpolation", so these are the lists for which the signs H_1 <= T_k and H_2 >= 0 are proved.

(P3) Equation `eq:uniform-derivative-bounds` (02), at j = 0. For real s >= 0, |p_a(s)| <= V and |K_{p_a}(s)| <= 3 e^{-.187 s} V, where V = 25|C| + 36 sum(|c_n| + |d_n|) <= 36 ||a||_1.

(P4) Section 03 defines q(k) = (v_1..v_5, v_1/k..v_5/k) with v_j = e^{-k(n_j - 1)}. Equation `eq:target-jet-bound` dominates the target jets J T_k by c_* e^{-2.36(n-1)}, uniformly in k >= 2.36.

### 1.3 Author deductions (checked, screening only)

(D1) Uniform profile bound. By (P3) and (P2), for all s >= 0 and k >= 2.36,
|H_1(s)|, |H_2(s)| <= 36 ||l_1|| + 108 ||l_2|| <= 108 (||l_1|| + ||l_2||) < 540.

(D2) Value at the origin. f_alpha(0) = k e^{-k} H_1(0) <= 540 k e^{-k}. Since k = pi(alpha/b - h), e^{-k} = e^{pi h} e^{-pi alpha/b}. The six minimal vectors give S(alpha) >= 6 e^{-pi alpha/b}. Hence

  f_alpha(0) <= 90 pi e^{2 pi/5} b^{-1} * alpha * S(alpha)   (alpha >= 1).

This has the form O(alpha S(alpha)), not O(S(alpha)). The extra factor alpha costs nothing after integration against any measure with finite lattice energy (D5).

(D3) Gaussian envelopes. For alpha >= 1, |f_alpha(x)| <= 540 k e^{-k} e^{-pi h b |x|^2} and |fhat_alpha(xi)| <= 540 k e^{-k} e^{-pi h b |xi|^2}. So ||f_alpha||_1 + ||fhat_alpha||_1 <= 1080 k e^{-k}/(hb). For 0 < alpha < 1, (P1) and (D3) at beta give
  |f_alpha(x)| <= G_alpha(x) + 540 beta k_beta e^{-k_beta} e^{-pi h b |x|^2},
  0 <= fhat_alpha(xi) <= alpha^{-1} e^{-pi|xi|^2/alpha} + 540 beta k_beta e^{-k_beta} e^{-pi h b |xi|^2}.
Here beta k_beta e^{-k_beta} is bounded on beta >= 1.

(D4) Continuity in alpha. The right side of the equation in (P2) is continuous from [2.36, infinity) to l^1. Coordinatewise continuity plus the uniform summable domination in (P4) gives continuity of J T_k, and q(k) is continuous. L^{-1} is fixed, so k -> (l_1, l_2) is continuous in l^1. The spectral measures depend linearly and boundedly on the lists in total variation (`lem:cardinal-measure`, `lem:kernel-bounds`), so H_i(s) is jointly continuous in (k, s). Hence (alpha, x) -> f_alpha(x) and fhat_alpha(xi) are jointly continuous on (0, infinity) x R^2, including at alpha = 1 by the duality formula. Uniqueness in (P2) makes the choice canonical, so no measurable-selection theorem is needed. (r128 used Jankov–von Neumann for the integrable class. That step is unnecessary here.)

(D5) Integration. Let g:(0,infinity) -> [0,infinity) be completely monotone with E_g(A) = sum_{a != 0} g(|a|^2) < infinity.
- Finite energy forces g(infinity) = 0. Bernstein's theorem then gives g(t) = integral over (0,infinity) of e^{-pi alpha t} dmu(alpha), with mu positive and no atom at 0.
- Small alpha. Poisson summation on A, with covolume one and A* = JA, gives sum_{a in A} G_alpha(a) = alpha^{-1} sum_{w in A*} G_{1/alpha}(w) >= alpha^{-1}. So S(alpha) >= alpha^{-1} - 1, which is >= 1/(2 alpha) on (0, 1/2]. On [1/2, 1], S(alpha) >= S(1) > 0 and alpha^{-1} <= 2. Hence the integral of alpha^{-1} dmu over (0,1) is at most C times the integral of S dmu, which equals C E_g(A) by Tonelli. In particular mu((0,1)) is finite.
- Large alpha. g(t_0) < infinity at t_0 = 1/(2b) < 1/b. Since k e^{-k} <= C e^{-pi alpha t_0} on alpha >= 1, the integral of k e^{-k} dmu over [1, infinity) is finite.
- Hence the integral of (||f_alpha||_1 + ||fhat_alpha||_1 + f_alpha(0)) dmu is finite, by (D2)–(D3). The Bochner (or plain Lebesgue–Fubini) integral f_g = integral of f_alpha dmu(alpha) defines a continuous radial f_g in L^1 with fhat_g = integral of fhat_alpha dmu in L^1.
- Pointwise, f_g(x) <= g(|x|^2) for x != 0, fhat_g >= 0, f_g = g(|.|^2) on A \ {0}, and fhat_g = 0 on A* \ {0}. By Tonelli (S >= 0) and the separate finiteness of the integral of f_alpha(0) dmu, fhat_g(0) - f_g(0) = integral of S dmu = E_g(A).
- Decay. By (D3), fhat_g has Gaussian decay for every such g, and |f_g(x)| <= g(|x|^2) + C e^{-pi h b|x|^2}. If g(t) <= C t^{-1-delta/2} for t >= 1, then f_g and fhat_g are admissible in the Cohn–Kumar sense. For g(t) = t^{-p} with p > 1, the decay is |x|^{-2p} with 2p - 2 > 0.

So the Cohn–Kumar per-potential sharp auxiliary exists for every completely monotone g with finite triangular-lattice energy. This includes every singular Epstein potential t^{-p}, p > 1. The source states its LP proposition for Schwartz f. Its proof (and the companion's) uses only that f is continuous and integrable, that fhat is integrable and nonnegative, and Fourier inversion. So f_g certifies the energy bound sharply for density-one competitors, and Cohn–Kumar Proposition 9.3 does the same for periodic ones in the admissible case. The energy inequality itself was already source090's theorem; f_g adds only the per-potential certificate. Note also |f_alpha(x)| <= f_alpha(0) = ||fhat_alpha||_1, so dominated convergence gives continuity of f_g.

### 1.4 Disposition: routine composition, not nominated

Each load-bearing step is a paid source operation or classical:
- the uniform list bound (P2);
- the j = 0 spectral bounds (P3);
- the duality lemma (P1);
- continuity of a fixed bounded inverse applied to continuous data;
- Bernstein's theorem;
- Fubini and Tonelli.

The only author contribution is to notice that (P2)+(P3) bound f_alpha(0) by O(alpha S(alpha)), and that this is enough. That is hypothesis removal through a known reduction, and the r129 brief's LESSON classes it as technical. It is not an integrated operation that the source and classical tools fail to supply. The r128 belief that a boundary-layer certificate was needed came from requiring O(S(alpha)) without the factor alpha. Under the source normalization f_alpha = k e^{-k} f, that requirement would mean f(0) = O(1/k), which nothing requires. A sharper bound f_alpha(0) = Theta(S(alpha)) may hold, but no target needs it, and it would be a quantitative refinement. I froze nothing and nominate nothing.

The integrable completely monotone class (r128 S3.2) is a special case of D5. The brief excludes it as a standalone nominee, and the singular extension adds no unpaid operation.

### 1.5 Adjacent source090 questions (not reopened)

- Periodic uniqueness: r128 S2 is a classical composition, and history I134/I137 declined it.
- Quantitative defect and crystallization questions: I134/I137 cover these, and they are technical by lesson.
- Schwartz regularity of f_g is impossible, because f_g = g on A \ {0} forces polynomial decay at lattice points for t^{-p}. This is trivial.
- Uniqueness of f_g in the full radial class fails, by Sardari's Theorem 1.7 as cited by the source.

None of these is a closable unpaid operation.

## 2. Second family: source191, higher-dimensional Heilbronn

### 2.1 Source

Source191 `01-introduction.tex` (read in full), Theorem `intro:main`, gives absolute eta, c_1 > 0 such that Delta(n) >= c_1 n^{-2+eta} for all large n. The mechanism has two congruence conditions. The first is a finite-field norm of the parabola (1, xi, xi^2) encoded in a base-B determinant digit, with SL_3 orbit mixing. The second is an auxiliary cap modulo q: Lemma `aux:cap` gives S in {0..w-1}^3 in F_q^3, |S| >= w^3/q, with no three distinct points on an affine line. Proposition `aux:weights` grades the weights by rank mod q. Proposition `zero:weighted-zero` and its lemmas count determinant-zero lifts through primitive null vectors and rank-two row lattices.

### 2.2 Author feasibility calculation (dimension three)

The direct analogue for four columns in Z^4 needs, modulo q, a box set S in F_q^4 of size about w^4/q (w ~ q/H^2) in which any four distinct points are affinely independent. That means no four points on an affine plane, which mirrors "no three on an affine line" for three columns. Distinct non-collinear triples of such an S determine distinct affine planes, because two triples on one plane would put four points of S on it. AG(4,q) has about q^6 affine planes, so |S|^3 <= 6 q^6 (1 + o(1)) and |S| = O(q^2). The required density w^4/q is of order q^3/H^8, so for fixed H and large q the direct cap design fails by counting. In dimension d the same count gives |S| = O(q^2) against a requirement of order q^d. This only refutes the direct transfer of Lemma `aux:cap`. It does not refute any rank-graded replacement or the three-dimensional target.

### 2.3 History (read late) and disposition

The alias search then found arithmetic r56/r57, which froze exactly this target (T191V56): four points of [0,1]^3, tetrahedra of volume >= c n^{-3+eta}. That archive is unresolved and records:
- the fourth-degree carry scale and Smith-divisor moment;
- lower-rank singular strata;
- an exceptional-normal loss of the natural auxiliary design;
- a Van de Voorde–Voloch comparison: 2q+1 points in PG(4,q) with no four coplanar, and an upper bound of order q^{3/2}.

The r56 auxiliary analysis already covers my counting obstruction in substance. It replaces the dense quadric by the sparser affine rational normal curve, with |S| >= w^4/q^3, and computes the resulting exceptional-normal loss O(N^12/I^3 * h^3 H^8), which enlarging q does not remove. Structural r24 rejected regular multiscale realizations. Following the brief, I do not reopen an old full gap without concrete work closing its entire scope. I have no such work, so this family stops at the screen. Credit goes to arithmetic r56/r57 and structural r24.

## 3. Why the round stopped

The optional focus turned out to be paid: the strongest generic reduction (integrate the source's canonical Gaussian pairs) closes the full per-potential scope through the source's uniform coefficient bound, so there is no unpaid operation to freeze. The second family is an existing open archive whose missing operations I could not close. Under the brief, freezing requires a genuine closable unpaid operation. None was found, so the round ends PREFREEZE with no nominee.
