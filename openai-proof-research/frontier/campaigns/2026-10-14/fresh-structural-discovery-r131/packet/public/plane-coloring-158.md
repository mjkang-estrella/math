# Family 158: transfer of densities and distance sets in the plane

This is a prefreeze screen. No exact target was frozen and nothing here is nominated or certified. The calculations in Sections 3 and 4 are feasibility sketches written to locate the strongest compatible consequence and the exact unpaid step. They are not presented as proofs.

## 1. Why this family

The family-level history search (Section 6 of `reading-limits.md`) found only one prior operative round on family 158. Structural r20 screened the weak-to-proper *completion* interface. It found that the Lebesgue completion is a primary duplicate (Davies 2610.12301v1 Lemma B.1; Koshelev–Kupavskii–Voronov 2610.18907v1 Lemma 7.1) and that Borel completion lacks an ambient selection mechanism. No round examined the forward transfer itself: its rigidity input, distance sets, independence density, fractional colouring, or arbitrary distance ratios. Family 157 (r44, r116, I22) and the other low-count structural families had already been screened, so 158 was chosen.

## 2. Stipulated source contract (actual text read)

Pinned source *The Euclidean plane is not five-colorable* (`build/sections/introduction.tex`, `spectral.tex`, `transfer.tex` read in full; `rigidity.tex` lines 320–618 read in full):

- `thm:main`: no proper 5-colouring of the plane; 6 <= chi(R^2) <= 7.
- `def:weak-coloring`, `thm:transfer`: for every k, a proper k-colouring exists iff a weak measurable k-colouring exists.
- `def:spectral-groups`: F = real algebraic numbers, E = F(i), K = unit elements of E, D = dual of E_disc, C = continuous characters.
- `thm:rigidity`: every K-invariant probability on D with nu(C) = 0 is Haar.
- `lem:palettes-continuous-factor`: the E-continuous vectors form L^2 of a rotation-invariant factor; the translations extend to a strongly continuous R^2 action preserving positivity.
- `prop:palettes-forward`: its proof derives, from rigidity, `<b_i, T_z b_i> = 0` for **every** z in E \ {0}, where b_i = f_i - E(f_i | F_c).
- `lem:palettes-density-proper`: full-density points of a weak class contain no unit pair.
- `lem:spectral-null-events`, `lem:line-average`, `lem:rigidity-general-position`, `lem:rigidity-capped-residues` and the completion of `thm:rigidity`.

## 3. Strongest compatible consequence (not nominated)

**Observation.** In the proof of `prop:palettes-forward`, rigidity kills every nonzero algebraic correlation of the discarded part b_i, and both cross terms vanish. Hence `<p_i, T_z p_i> = <f_i, T_z f_i>` for every z in E \ {0}. Nothing in that step uses that |z| = 1. Unit length enters only when properness is invoked.

Consequences, by re-running the source proof with a different invariant system:

(a) *Distance sets in F.* Let D be a set of positive real algebraic numbers. A proper colouring of the plane's D-distance graph yields a law on proper labelings of E with `<f_i, T_{du} f_i> = 0` (d in D, u in K). The same projection, continuity extension and sampling give a weak measurable D-colouring. Density points avoid all of D. With the completion of Davies B.1 or KKV 7.1 (stated for distance sets in the former), this gives chi_D(R^2) = chi_D^(m)(R^2) for D in F.

(b) *One independent set.* Let every finite unit-distance graph in the plane have independence ratio at least a. Følner averaging over E and then over K gives an E ⋊ K-invariant law mu on unit-independent subsets of E with mu(0 in I) >= a. Then p = E(f | F_c) satisfies `<p, T_u p> = 0` on S^1 and has mean at least a. The jointly measurable field H(x, omega), reverse Fatou over centred squares, and one sample give a weak unit-avoiding measurable set of upper density at least a. The density-point step (same proof as `lem:palettes-density-proper`, applied to one class) makes it unit-avoiding everywhere. Hence alpha(R^2) <= m_1(R^2), and the classical reverse inequality gives alpha(R^2) = m_1(R^2). This is the planar form of Davies's Theorem 1.1 density statement, which he proves only for d >= 4.

(c) *Compositions.* The following are then routine:

- chi_f(R^2) >= 1/alpha(R^2) = 1/m_1(R^2). Periodizing a near-extremal measurable set and taking a random translate gives the reverse inequality, so chi_f(R^2) = 1/m_1(R^2). With the Ambrus–Csiszárik–Matolcsi–Varga–Zsámboki bound m_1 <= 0.2470 (abstract only) and Croft's 0.22936, this gives 4.048 <= chi_f(R^2) <= 4.360.
- Colour-dependent distances: there is no 4-colouring with colour i avoiding distance d_i, for arbitrary reals d_1, ..., d_4 > 0. Scaling makes each alpha equal to alpha(R^2). The generic Minkowski sum V_1 + ... + V_4 of rotated near-extremal finite sets is partitioned into isometric copies of each V_i, so the classes cover at most 4(m_1 + eps)|V| < |V| points.
- Davies's Theorems 1.2 and 1.3, with his Theorem 1.1 replaced by (a)/(b). For algebraic, well-separated D with |D| = k, Bukh's measurable theorem (via Davies's statement only) gives chi_D(R^2) >= (m_1 + eps)^(-k). Also, every finite colouring of the plane has a monochromatic pair at every sufficiently large real algebraic distance. For the second statement, feed the unbounded set of bad algebraic distances into (a) and apply the classical Furstenberg–Katznelson–Weiss positive-density theorem to a class of positive upper density. Davies's odd-distance theorem is a special case.

## 4. Strongest generic reduction and why (a)–(c) stop

Every item above has the shape *source transfer, re-run verbatim per distance, plus an external measurable theorem or classical compiler*.

- The source pays the integrated operation: rigidity, the continuous factor, preservation of correlations, measurable sampling and density points.
- KKV (16) pays the density-sum step for colourings. Davies pays the composition "transfer + Bukh" (Theorems 1.2, 1.3) and the completion (B.1).
- Følner correspondence, reverse Fatou, periodization and Minkowski sums are classical.

The only new arithmetic is that the per-colour proof never used |z| = 1. Under the campaign's i256 calibration (LESSON in the brief), such black-box compositions are TECHNICAL however strong their headlines. Freezing any of them would contradict the brief's "if and only if a genuine closable unpaid operation exists" rule. None is nominated.

## 5. The genuinely unpaid operation: transcendental distance ratios

For D containing F-linearly independent distances (for example {1, tau} with tau transcendental), every item above loses its proof. The exact failures are as follows.

(i) **Restricting to E'' = sum_j d_j E fails the rigidity contract.** E'' is isomorphic to E^m as a K-module, with characters D^m, and its continuous characters are C'' = {(j(xi), j(tau xi))}. Take nu = lambda x Haar, where lambda is the radial law of j(xi) with |xi| = rho. It is K-invariant and has nu(C'') = 0. Its coefficient at (u, 0) is J_0(rho) times a nonzero factor, which is generically nonzero. So a wild discarded part can carry correlation at a forbidden displacement. This refutes only reuse of the source contract on E''. It does not show that the transfer fails.

(ii) **The field route needs new rigidity.** Let F' be the real closure of Q(D), E' = F'(i), K' its unit group. The parts of the proof I read (`lem:spectral-null-events`, `lem:line-average`, the location lemma, relative singularity, the radial identities and capped residues) use only that F' is a countable real-closed subfield of R. The completion of `thm:rigidity` does not. It chooses "a number field N_0 ⊂ F containing the real and imaginary parts of every q_j". It also needs `lem:rigidity-general-position` with d_0 = [N : Q] finite. That makes 1 a bounded integer combination of any d_0 good rotations. With transcendental syndetic transversals q_j, no finite-dimensional rational space contains q_j S for a large unit set S in general position. Two repairs fail:

- *Restricting to K_alg.* Følner sets of K_alg are not Følner in K', so `eq:source-9` is unavailable.
- *Line averages over F_alg-lines in E'.* The null-event step needs L_a ∩ L_b ⊂ C'. For F_alg-lines, continuity on two lines gives continuity only on a 4-dimensional F_alg-subgroup, not on E'.

Lines 1–319 of `rigidity.tex` (the compact tower) were not read, so their field-generality is unverified.

(iii) **The target may be false.** If rigidity held over every countable real-closed F', then (a) and (b) would hold for every finite D. Davies writes that a conjecture of Bukh suggests that some extra algebraic condition on D may be necessary. I did not read Bukh's conjecture, so it is not used, but it signals that the full-generality statement may be false.

So the full statement "alpha_D(R^2) = m_D(R^2) for every finite D", and its chromatic form, is not closable here. It is either a new rigidity theorem over transcendental fields or a counterexample to it. Neither was constructed, and no restricted (algebraic-D) version is nominated in its place.

## 6. Outcome

PREFREEZE, no nominee. The strongest compatible consequences are routine compositions. The one unpaid integrated operation is unbuilt and possibly false. Failures of particular routes are not impossibility claims for the targets.
