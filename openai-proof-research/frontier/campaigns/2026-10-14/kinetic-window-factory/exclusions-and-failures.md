# Exclusions, residual risks, and the exact fallback lemmas

Date: 2026-10-14. Companion to `candidate.md` (status CANDIDATE, UNREVIEWED).

## 1. Shortcuts that remain excluded

None of these is used in `candidate.md`. Items 1–8 repeat I340's recorded
failures (`frontier/experiments/i340_kinetic_path_fluctuations/reading-and-failures.md`);
items 9–12 are from this run.

1. **Small jumps imply tightness.** Each collision changes the field by
   $O(\mu^{-1/2})$, but small jumps give no modulus of continuity. Many
   particles can jump in a short window. Proposition M bounds the number of
   jumping particles instead.
2. **Martingale or Aldous criteria.** The dynamics is deterministic with a
   random initial law. No collision-current martingale is available, and no
   stopping-time conditional estimates were obtained.
3. **BGSS short-time functional theorem** (arXiv:2008.10403v2). It covers short
   times on the torus. It does not cover the full DHM-regular lifespan in the
   whole space. Its §8.2 point-3 time factor uses a localized creation or
   clustering time. That was not shown to survive H's layered representation
   when the marked event is a redundant contact.
4. **BGSS stationarity patching** (arXiv:2201.04514v1). It is an equilibrium
   mechanism. The target is out of equilibrium.
5. **DHM/H primitive close-pair gain.** H's primitive type-A pair is freely
   parameterized and its gain needs a velocity-volume restriction. Two
   arbitrary events in a tiny window are not covered. No extension is asserted.
6. **"No cycle on a good event."** H's small connected-cycle *measure* is a
   statement about a signed expansion. It is not a bound on the probability
   that the gas has no recollision.
7. **Independent restart in each slab.** The interface law is the evolved,
   correlated exclusion ensemble, not a fresh product activity.
8. **Qualitative $r_\varepsilon$ inside GRR at a microscopic cutoff.** With
   $\gamma=7/3$ and $\alpha=\mu^{-7/3}$, GRR amplifies the remainder by
   $\alpha^{1-\gamma}=\mu^{28/9}$. A qualitative $r_\varepsilon\to0$ cannot pay
   this. `candidate.md` replaces $r_\varepsilon$ by $C_P\varepsilon^P$
   (Proposition I), so the issue disappears there, but the shortcut itself
   stays excluded.
9. **A fresh, independent time for a redundant contact.** A redundant contact
   has no free parameter in H's chronological chart. Giving it one changes the
   measure. Lemma W never does this: it shifts all event times of the whole
   connected history together, which is a measure-preserving change of
   variables (Claims 2–3).
10. **Shifting only the marked line, or one sub-cluster.** This was tried and
    dropped. Moving part of a connected history in time breaks the contact
    equations of the links that join it to the rest, so the shifted point is not
    a history of the same diagram. Only the global translation is
    covariant.
11. **Second-moment union bound for the microscopic modulus.** At
    $\alpha=\mu^{-3/2}$ a second-moment Markov bound gives
    $(T/\alpha)\,\mu\alpha/(\eta^2\mu)=T\mu^{1/2}/\eta^2\to\infty$. The third
    moment is needed and gives $\mu^{-1/2}$ (Proposition M).
12. **Testing $c_h^\varepsilon$ with two-record functions.** H's marks are a
    single additive scalar $y$ (`eq:limit-mark-update`). A function such as
    $\mathbf 1\{z(t)\ne\Phi^0_\delta z(s)\}$ is not a function of
    $(x,v,y)$ at the final time. Proposition I uses it only as a pointwise
    bound on formal histories inside diagrams, and tests $c_h^\varepsilon$
    only with powers of $y$. (An earlier draft of Proposition I phrased this
    loosely; it was corrected before this file was written.)

## 2. Residual risks, in decreasing order

- **R1, Lemma W core (highest).** The argument enlarges H's integrand to a
  formal extended history (`F_G ≤ F_G^ext`), drops lifetime, segment and
  chronology constraints, and reruns H's flux-tree and fresh-label counting on
  the enlarged integrand. A reviewer must check:
  (a) H's flux-tree bound (`lem:sharp-factorials`) is taken at fixed times,
  normals and birth velocities, and uses only energy conservation and the
  fact that redundant contacts are determined by earlier data;
  (b) H's link coordinate $y_l$ is the difference of affine origins at time
  $0$ (H §06, lines 168–173), so the shift moves it by $-\theta u_l$;
  (c) the forward-ray rule agrees with the physical redundant time on the
  physical domain (Claim 1);
  (d) the cylinder replacement keeps the per-link factor at
  $\mu^{c-h}C\prod_l(1+|v_{p_l}|+|v_{q_l}|)$ with $c=1$.
- **R2, uniformity in pulse times.** Remainders (a)–(c) of
  `thm:marked-expansion` must be uniform in the two pulse times. I340 §6 made
  the same claim; it was not re-proved here.
- **R3, Lemma E′.** This is the only extension of H's literal statements: a
  final-slab test of root *histories* (velocity jump in $(a,b]$), justified
  from `lem:autonomous-partition` (eq. `autonomous-observation`) and the proof
  of `lem:one-slab-expansion`. It is used only for Proposition M.
- **R4.** Absorbing $\prod_l(1+|u_l|)$ over at most $2K$ lines into the
  reserved Gaussian does not change the per-atom exponential base.
- **R5.** Moment–cumulant relation for factorial measures with the jump test;
  `eq:limit-factorial-ordinary` for the two-pulse scalar mark.
- **R6.** Exponent arithmetic in Lemma C and Proposition M
  ($\alpha=\mu^{-3/2}$, $\theta=1/8$, $P>6$).

## 3. What remains if a reviewer rejects a step

**If Lemma E′ is rejected** (Lemma W accepted). Proposition I, the
fourth-moment bound, the transfer, and identification all stand. The exact
missing statement is:

> **Missing Lemma M\*.** For the pasted dynamics of H `thm:marked-expansion`
> and each real $\phi\in C_c^\infty(\mathbb R^6)$, there exists
> $\alpha_\varepsilon=\mu^{-A}$ for some fixed $A>1$ such that
> $w(\widehat X^\varepsilon(\phi),2\alpha_\varepsilon)\to0$ in probability.

Any $A$ suffices: Lemma C works with any $\theta\in(0,1/4)$ such that
$\mu^{-1}\alpha_\varepsilon^{-4\theta}\to0$, and the $\varepsilon^P$ remainder
is arbitrary-order. A sufficient condition is, for some integer $q\ge3$ and
all intervals $I$ inside one slab with $|I|\le3\alpha_\varepsilon$,
$$
\mathbb E[\mathrm{Count}(I)^q]\le C\bigl(\mu|I|+\mu^q\varepsilon^P\bigr),
$$
because the union bound then gives $(T/\alpha)\,\mu\alpha/(\eta\sqrt\mu)^q=
T\eta^{-q}\mu^{1-q/2}\to0$. Proving it needs H's expansion for a test that
dominates a velocity jump over a whole window. A two-record replacement for the
jump indicator is not available within H's scalar marks (item 12).

**If Lemma W is rejected.** Then the exact missing statement is Lemma W itself,
the marked-contact window estimate:

> **Missing Lemma W.** For fixed $h$, $K$, and records, uniformly in pulse
> times and in bounded intervals $J$,
> $\sum_{\mathsf D\in\mathfrak D_K}\int N_J(\ell)\,d|\mathsf D|\le C\mu^{1-h}|J|$,
> where $N_J(\ell)$ counts C-atoms on the designated line with time in $J$,
> **including redundant contacts**.

Without it, Proposition I falls back to I340's qualitative bound with
$r_\varepsilon$, and the full target returns to I340's status: continuous
Gaussian version and exact-centering transfer paid; window estimate and
microscopic modulus unpaid.

## 4. What is not claimed

- No acceptance. No independent proof review or contribution review has run.
- No novelty claim. Whole-history time-translation averaging may already
  appear in the BGSS cumulant papers or elsewhere; this was not searched.
- The numerical checks in `checks/` are illustrations only.
- No statement about the true dynamics beyond what H `prop:cutoff` and I340's
  transfer give.
