# Reviewer operation-level contribution comparison (P6)

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

**Contribution verdict: TECHNICAL.** PCW is a correct and complete
process-level statement that no read primary body or pinned blob states.
Its proof, however, assembles operations that are each established and
short to adapt. The decisive increasing-depth whole-path replacement is an
elementary combination, not a new mechanism. A missing exact duplicate is
not treated as novelty.

## Operation table

| PCW step | What PCW does | Established antecedent (read body) | Difference | Weight |
|---|---|---|---|---|
| O1 scalar normal form (§3) | Second/fourth moment recursions; R=3Q^2; forcing t=((b-1)/b)Q^2 | Yu–Polyanskiy near-critical, Lemma 2 (all even moments Gaussian by multinomial expansion with odd terms via symmetrization), Lemma 3 (E R^2=dE F^2+d(d-1)((1-2delta)E F)^2, eq. 21) | Small parameter is observation strength at exact criticality instead of distance to criticality. In half-LLR units YP gives (perturbation)·Q=((d-1)/d)Q^2. The quadratic coefficient is identical; only the linear forcing changes. | Antecedent, credited by author |
| O2 a priori moments, path maxima (§2.1) | Doob + Gaussian tail upgrade fixed-time moments to sup-moments | Source `lem:critical-tail` (all moments); Doob | Routine | Standard |
| O3 whole-history tilt (§2.2) | Density 1+eta M(s) on component history | Source `lem:component-spin-tilts` (fixed time); NSZ Lemma 2.1 (posterior via Girsanov likelihood); JKLM Lemma 23 setting P_U P_V (1+a_u b_v) | Same one-line Bayes identity on a larger sigma-field | Standard |
| O4 depth linearization (§5 expansion) | Y_o ≈ theta^n sum Y_u, absolute-sum error C sqrt(N)(sqrt(s)+s^(3/4)) | YP Remark 2: R ≈ sum_(d^k) R_u/sqrt(d^k) "leading to normal distributions by central limit theorem"; Janson–Mossel Lemma 2.7 (product linearization near trivial) | PCW makes the heuristic quantitative in L^2 sup-norm by the triangle inequality, using source moments | Technical |
| O5 planted-to-independent replacement (§5 TV) | Product of tilts 1+eta_u M_u, TV <= sum E|M_u|, mixture over correlated cut spins | JKLM Lemma 5 / Lemma 23: tilted pair density (1+a_u b_v) is W_p-close to the independent sum when moments are small; iterated level by level near criticality | PCW applies the same "weak tilt is close to product" mechanism once at a growing cut, in TV, which is cruder and simpler than JKLM's Wasserstein estimate | Technical |
| O6 balancing depth (§5) | One n=floor(log_b(1/eps)/8) controls sqrt(N)eps^(1/4) and N eps^(1/4) | Standard choice of a growing truncation level | Two polynomial errors, one logarithmic depth | Routine |
| O7 path-level CLT (§4) | Independent continuous martingales, BDG bracket concentration, DDS time change | Whitt Theorem 2.1 (triangular martingale FCLT, convergence of quadratic variation to a deterministic continuous limit); Ethier–Kurtz 7.1.4 | PCW gives a self-contained continuous-path special case; author also labels it standard | Standard |
| O8 joint spatial law (§6) | Finite-hull linearization, boundary decoupling by the same tilt-TV, finitely many independent limits | Same as O4/O5 with a fixed finite boundary | Finite, elementary | Technical |
| O9 covariance and wave (§7) | b theta^2=1 boundary conservation; phi_d; harmonic identity at 2 sqrt(b) | Elon Theorem 1.1, Lemmas 2.1–2.2 at lambda=2 sqrt(b) | Identification only; no new covariance | Antecedent |
| O10 observation model | X=t sigma+B, posterior drift m | Nam–Sly–Zhang §2.2, Lemma 2.1; source family236 | Same model | Antecedent |

## Is the simultaneous whole-path replacement substantial?

The parent asked whether increasing-depth whole-path replacement
(O4+O5+O6+O7 together) is a substantial mechanism. Assessment:

1. **The time structure is forced by known ingredients.** Each summand is
   a bounded continuous martingale in its own filtration (source). Any
   triangular array of independent such martingales with
   E L(t)^2→kappa sqrt t and bounded fourth maxima converges to
   B(kappa sqrt t) by the classical FCLT. Once the scalar variance is known
   (O1), the sqrt(min(s,t)) clock carries no further information.
2. **The decoupling is the known weak-tilt mechanism.** JKLM's Lemma 23 is
   exactly the statement that a planted pair with density (1+a b) is close
   to the independent pair when moments are small. PCW uses the simplest
   version, total variation of a product of densities 1+eta M, which costs
   E|M| per factor. The argument is three lines. It is valid for whole
   histories because the density is the terminal-time posterior.
3. **The linearization is YP's Remark 2, made quantitative by the triangle
   inequality.** PCW's version deliberately avoids any independence at
   internal vertices. That is a sound design choice, but it is a cost
   accounting, not a new idea. The source's all-moment lemma makes it work.
4. **Spatial identification is elementary** once O4/O5 hold. The covariance
   is Elon's spectral-edge wave, and hull consistency is one line from
   b theta^2=1.
5. **What is genuinely new to this project** is the combined statement:
   the critical NSZ posterior field, rescaled by eps^(-1/4) at times eps t,
   converges as a process to the critical Gaussian wave with Brownian
   sqrt(t) clock, jointly in space and time, under the actual planted law.
   The reviewer found no read body stating it. YP's papers treat scalar
   fixed-point distributions at a single parameter value; JKLM concerns
   bounded-memory reconstruction; NSZ and source family236 treat factor
   construction and do not take small-time scaling limits; Elon constructs
   the wave abstractly. This supports "not DUPLICATE", not "substantial".

A complete elementary proof may still be technical (review brief). That
is the case here: every step is short given the antecedents, and the
author's own comparison already credits most of them. The remaining
combination is careful but routine for the area.

## Limits

Bounded reading only (see `source-reading.md`). No full citation chase of
YP or JKLM predecessors (for example Mossel–Peres, Sly, or the
Gu–Roozbehani–Polyanskiy conjectures). A process-level statement of this
exact form could exist in literature not read here; the verdict would then
move toward DUPLICATE, not toward SUBSTANTIAL. No novelty claim beyond
"new to this project" is made.
