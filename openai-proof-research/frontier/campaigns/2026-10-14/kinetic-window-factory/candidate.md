# Kinetic window closure by time-shift averaging — candidate proof

Date: 2026-10-14. Pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Author role: Factory/Opus 5.5 fallback research sub-agent (no child agents).

**Status: CANDIDATE, UNREVIEWED.** This file proposes a complete argument for
the original I340 target. It has had no independent proof review and no
contribution review. It must not be counted until both gates pass. One step
(Lemma E′, used only for the microscopic modulus) is an explicitly flagged
reading of H's one-slab identity beyond the literal pulse-record wording of
H's §04; see §4 and `exclusions-and-failures.md` for what remains if a reviewer
rejects it.

H denotes `preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/sections`
at the pin. Upstream theorem truth is stipulated. Every deduction below is new
to this file unless credited.

---

## 0. The exact target (unchanged from I340)

Phase space is $\mathbb R^3_x\times\mathbb R^3_v$, sphere diameter $\varepsilon$,
$\mu=\varepsilon^{-2}$. The initial law is H `eq:grand-canonical`:
$\mathcal Z_\varepsilon^{-1}\frac{\mu^N}{N!}\mathbf 1_{\mathcal D_N^\varepsilon}\prod f_0(z_i)\,dz_i$,
including $N=0$. H `ass:kinetic` holds: $f_0\ge0$ smooth probability density,
$\|f_0\|_{\mathrm{Bol},2\beta}+\|\nabla_xf_0\|_{\mathrm{Bol},2\beta}<\infty$, and a
nonnegative classical Boltzmann solution with
$\sup_{t\le T}\sup_{x,v}e^{2\beta|v|^2}f_t<\infty$ on the **entire supplied**
$[0,T]$. No shortening of $T$, equilibrium, periodic box, smoothing in time, or
modified gas is introduced. Dynamics: deterministic elastic hard spheres.

For real $\phi\in C_c^\infty(\mathbb R^6)$,
$X_t^\varepsilon(\phi)=\zeta^\varepsilon_t(\phi)=\mu^{-1/2}\bigl[\sum_i\phi(z_i(t))-\mathbb E\sum_i\phi(z_i(t))\bigr]$
with **exact** microscopic centering at every $t$.

**Theorem F (candidate).** For every finite list
$\phi_1,\dots,\phi_m\in C_c^\infty(\mathbb R^6;\mathbb R)$,
$$
\bigl(X^\varepsilon_\cdot(\phi_1),\dots,X^\varepsilon_\cdot(\phi_m)\bigr)
\Longrightarrow
\bigl(\zeta_\cdot(\phi_1),\dots,\zeta_\cdot(\phi_m)\bigr)
\quad\text{in }D([0,T],\mathbb R^m)\text{ with the }J_1\text{ topology},
$$
where $\zeta$ is the continuous version (I340 analysis §2) of the centered
Gaussian field of H `thm:main`. The sequence is moreover C-tight, so the
convergence also holds for the uniform topology.

H `thm:main` gives finite-dimensional convergence only. Theorem F needs
C-tightness. The proof below obtains it from a new window estimate (Lemma W)
that pays **every** marked contact time, including redundant contacts whose
time is determined by earlier mergers.

---

## 1. Inputs used

From H (statements read at the pin; truth stipulated):

| Label | Use |
|---|---|
| §03 `def:dhm-history`, `eq:edge-integral`, `eq:normalized-history` | history integrals, activity/normalization |
| §03 `thm:dhm-package`, `lem:dhm-dummies` | positive coarse bounds; a bounded multiplier costs its supremum |
| §04 `lem:autonomous-partition` (eq. `autonomous-observation`), `lem:one-slab-expansion` | exact one-slab identity for tests of root histories |
| §04 `lem:marked-regrouping`, `lem:diagram-labels`, `lem:stopped-variation`, `thm:marked-expansion` | exact connected expansion and remainders |
| §06 `eq:sharp-initial-link`, `eq:sharp-merger-count`, `eq:sharp-activity`, `lem:sharp-merger-coordinates`, `eq:sharp-scaling`, `lem:sharp-factorials`, `lem:sharp-summability`, `thm:sharp-cumulants` | chronological merger chart and summable majorant |
| §07 `eq:limit-mark-update`, `eq:limit-factorial-ordinary` | two-pulse marks and factorial-to-ordinary cumulants |
| §02 `prop:initial`, `eq:initial-N-moments` | moments of $N/\mu$ |
| §05 `prop:cutoff` | $P(\text{true}\ne\text{pasted on }[0,T])\le C\varepsilon^{1+\eta}$, $\eta=1/20$, for every fixed $L\ge L_0$ |
| §01 `thm:main` | FDD convergence of the true field |

From I340 (parent-verified, credited, re-derived here only where needed):
the continuous Gaussian version (analysis §2) and the uniform exact-centering
transfer $\|X^\varepsilon-\widehat X^\varepsilon\|_\infty\to0$ in probability
(analysis §3, exponent $1/440$ with $p=22$).

Notation. $\widehat{\ }$ marks the pasted dynamics of H `thm:marked-expansion`
with its own exact centering. $\tau=T/L$. $c_h^\varepsilon$ is H's normalized
ordered factorial cumulant measure (normalization $\mu^{-h}$) of the pasted
process with records. "Retained connected diagrams" are those of H
`thm:marked-expansion`(ii). For a diagram $\mathsf D$, $|\mathsf D|$ is its
absolute history measure: inputs replaced by absolute values and all
$[0,1]$-valued weights (acceptance, compatibility leftovers) bounded by one,
exactly as in H §06.

---

## 2. Lemma W: time-shift averaging of a marked contact

### 2.1 Statement

Fix $h\ge1$, a complexity bound $K$, the initial-link sharpness $D$ of H
`eq:sharp-initial-link`, and any finite list of bounded records on the $h$
designated labels. Let $\mathfrak D_K$ be the retained globally connected
diagrams of order $h$ with $\rho\le K$, after replacing each nontrivial initial
cumulant by the forest domination `eq:sharp-initial-link` and keeping only its
physical-link (indicator) terms. For a designated label $\ell$ and a bounded
interval $J\subset\mathbb R$ let $N_J(\ell)$ be the number of C-atoms on the
line $\ell$ whose time lies in $J$; on each diagram this is a function of its
parameters.

**Lemma W.** There is $C=C(h,K,D,L,T,\text{kinetic bounds})$, independent of
$\varepsilon\le\varepsilon_0$, of $J$, and of all record and pulse times, with
$$
\sum_{\mathsf D\in\mathfrak D_K}\int N_J(\ell)\,d|\mathsf D|
\;\le\;C\,\mu^{1-h}\,|J|.
$$

The C-atom may be a merger **or a redundant contact**. No cycle-vanishing,
rate for cycles, or microscopic input is used.

### 2.2 The chart and an extended integrand

Fix one diagram $G$: its lines, C/O flags, slab assignments, chronological
order, the merger/redundant classification, its physical initial-link forest,
the designated label $\ell$, and one marked C-atom $a_*$ on $\ell$. Summing
$\mathbf 1\{t_{a_*}\in J\}$ over the C-atoms $a_*$ on $\ell$ gives $N_J(\ell)$.

H `lem:sharp-merger-coordinates` gives coordinates
$$
\xi=(v,X,y,(t_g,\omega_g)_{g})\in\mathbb R^{3m}\times\mathbb R^3\times\mathbb R^{3p}\times(\mathbb R\times S^2)^{a},
$$
namely birth velocities $v=(v_p)$, one absolute translation $X$ (the component
is connected), one relative vector $y_l$ per physical initial link (the
difference of the two lines' affine origins at time $0$, lines being born at
$0$), and $(t_g,\omega_g)$ per dynamic merger, with Jacobian
$\varepsilon^2[(\Delta v_g)\cdot\omega_g]_+dt_gd\omega_g$ at each merger and no
free parameter at a redundant contact. By `eq:sharp-activity`–`eq:sharp-scaling`,
$$
\int \mathbf 1\{t_{a_*}\in J\}\,d|\mathsf D_G|
\le C_K\,\mu^{m-h}\varepsilon^{2(m-1-p)}\int F_G(\xi)\,
\mathbf 1\{t_{a_*}(\xi)\in J\}\,d\xi ,
$$
where $F_G$ is the product of: the absolute birth inputs ($|g_i|$ or $f_0$)
evaluated at the physical birth positions; the link indicators
$\mathbf 1\{|y_l|\le R_{K,D}\varepsilon\}$; the merger fluxes
$[(\Delta v_g)\cdot\omega_g]_+$; and $[0,1]$-valued indicators (domain, segment,
lifetime, chronology, acceptance, redundant-contact existence). Record
multipliers are bounded by $1$ after the prefactor.

**Formal history.** For every $\xi$ (not only physically admissible ones) run
H's chronological construction with all lines extended to $\mathbb R$: before
its first event a line is the backward continuation of its birth segment, and
after its last event it continues straight. Process the events in the
prescribed order. A merger sets the relative translation of the two groups by
H's contact equation $X-X_*=-d(t_g)-\varepsilon\omega_g$, then reflects
velocities if it is a C-atom. A redundant contact between lines $p,q$ (already
in one group) is placed at the **forward-ray time**: the unique entering time
of $|r(t)|=\varepsilon$, $r(t)=x_p(t)-x_q(t)$ the straight relative flight with
current velocities, among $t\ge t_0$, where $t_0$ is the later of the two lines'
previous event times ($-\infty$ if none). If it does not exist, set the
redundant-existence indicator $R^{\rm ext}(\xi)=0$.

Define
$$
F_G^{\rm ext}(\xi)=\prod_p|g_{(p)}(x_p^\xi(b_p),v_p)|\prod_l\mathbf 1\{|y_l|\le R\varepsilon\}
\prod_g[(\Delta v_g)\cdot\omega_g]_+\;\mathbf 1\{t\in\mathcal D\}\;R^{\rm ext}(\xi),
$$
where $b_p$ is the birth time of line $p$ and
$\mathcal D$ = {each merger time in its assigned slab, mergers in their
prescribed relative order}. Let $t^{\rm ext}_{a_*}(\xi)$ be the formal time of
$a_*$.

*Claim 1: on the physical chart domain, $F_G\le F_G^{\rm ext}$ and
$t_{a_*}=t^{\rm ext}_{a_*}$.* Every factor of $F_G$ not displayed in
$F_G^{\rm ext}$ is in $[0,1]$. On the physical domain the formal paths agree
with the physical ones on each line's lifetime. A physical redundant contact
lies on its common segment interval, which is contained in $[t_0,\infty)$; a
straight relative flight has at most one entering time; so the physical time
is the forward-ray time. ∎

### 2.3 The shift map

For $\theta\in\mathbb R$ let
$$
\Phi_\theta(v,X,y,t,\omega)=\bigl(v,\;X-\theta v_{\rm rep},\;(y_l-\theta(v_{q_l}-v_{p_l}))_l,\;t+\theta\mathbf 1,\;\omega\bigr),
$$
$v_{\rm rep}$ the birth velocity of the representative line, $(p_l,q_l)$ the
endpoints of link $l$.

*Claim 2 (covariance).* The formal history of $\Phi_\theta\xi$ is the time
translate of that of $\xi$: $x_p^{\Phi_\theta\xi}(s)=x^\xi_p(s-\theta)$ for all
$p,s$, and all velocities after each event coincide. In particular every
redundant time and $t^{\rm ext}_{a_*}$ increase by exactly $\theta$, all fluxes
and $R^{\rm ext}$ are unchanged.

*Proof.* Let $\mathcal H$ be the formal history of $\xi$ and
$S_\theta\mathcal H$ its translate. Every defining relation of the formal
construction is invariant under time translation: straight flight, the contact
equation at a merger (it involves only relative positions at the contact time
and the normal), the reflection rule, and the forward-ray rule (its starting
time $t_0$ is an event time or $-\infty$). Birth times enter none of these
relations, because lines are extended to $\mathbb R$. Thus $S_\theta\mathcal H$
satisfies the defining relations for the same combinatorial data. Its chart
coordinates are read off directly: birth-segment velocities are unchanged;
merger times are $t_g+\theta$; merger normals are unchanged; the affine origin
at time $0$ of a line's birth segment becomes $x_p(-\theta)=X_p-\theta v_p$,
which gives the stated $X$ and $y_l$. The construction from coordinates is
deterministic (H's inductive proof; multiplicity one), so the formal history of
$\Phi_\theta\xi$ is $S_\theta\mathcal H$. ∎

*Claim 3 (measure).* For fixed $v$, $\Phi_\theta$ is a translation of
$(X,y,t)$ and the identity on $(v,\omega)$. It preserves
$d\xi=dv\,dX\,dy\,dt\,d\omega$. ∎

The physically meaningful content is simple: the history integrand is
invariant under translating a whole connected history in time, except through
the absolute positions where births and links are evaluated and through slab
membership. The next step shows these three exceptions cost only a polynomial.

The covariance was also checked numerically on random formal charts with up to
five lines (`checks/`). That is an illustration, not part of the proof.

### 2.4 Averaging over the shift

Fix $\Theta=\tau$. For each $\theta\in[0,\Theta]$, Claim 3 and the substitution
$\xi=\Phi_\theta\eta$ give
$$
I:=\int F^{\rm ext}_G(\xi)\mathbf 1\{t^{\rm ext}_{a_*}(\xi)\in J\}d\xi
=\int F^{\rm ext}_G(\Phi_\theta\eta)\,\mathbf 1\{t^{\rm ext}_{a_*}(\eta)+\theta\in J\}\,d\eta .
$$
Average over $\theta\in[0,\Theta]$ and integrate $X$ first. By Claim 2,
$x_p^{\Phi_\theta\eta}(b_p)=X+d_p$, with $d_p$ depending on
$(v,y,t,\omega,\theta)$ but with unit coefficient in $X$. Integrate one input in
$X$ and take the spatial supremum of the others. This is exactly H's step in
`lem:sharp-summability`:
$$
\int dX\prod_p|g_{(p)}(X+d_p,v_p)|\le \|g_{(p_0)}(\cdot,v_{p_0})\|_{L^1_x}\prod_{p\ne p_0}\|g_{(p)}(\cdot,v_p)\|_{L^\infty_x}
=:B(v),
$$
which is independent of $d_p$, hence of $\theta$. With Bol envelopes,
$B(v)\le C^m e^{-bE_0}$, $E_0=\sum_p|v_p|^2$. Next, for every
$\theta\in[0,\Theta]$,
$$
\mathbf 1\{|y_l-\theta u_l|\le R\varepsilon\}\le\mathbf 1\{y_l\in\mathrm{Cyl}_l\},
\qquad \mathrm{Cyl}_l=\{y:\operatorname{dist}(y,[0,\Theta]u_l)\le R\varepsilon\},
$$
with $u_l=v_{q_l}-v_{p_l}$ and
$|\mathrm{Cyl}_l|\le\pi R^2\varepsilon^2\Theta|u_l|+\tfrac43\pi R^3\varepsilon^3$.
Finally,
$$
\int_0^\Theta \mathbf 1\{t+\theta\mathbf 1\in\mathcal D\}\,\mathbf 1\{t^{\rm ext}_{a_*}+\theta\in J\}\,d\theta
\le |J|\;\mathbf 1\{t\in\mathcal D_\Theta\},
\qquad \mathcal D_\Theta:=\mathcal D-[0,\Theta]\mathbf 1 .
$$
Fluxes and $R^{\rm ext}$ do not depend on $\theta$. Therefore
$$
I\le\frac{|J|}{\Theta}\int dv\,B(v)\int dy\prod_l\mathbf 1_{\mathrm{Cyl}_l}(y_l)
\int_{\mathcal D_\Theta}dt\int d\omega\prod_g[(\Delta v_g)\cdot\omega_g]_+\,R^{\rm ext}.
\tag{W1}
$$

**Minkowski volume.** If $S=\{s<t_1<\dots<t_a<s+\tau\}$, then in gap
coordinates $t_k=t_1+u_k$ the $t_1$-range for fixed gaps has length
$\tau-u_a$ in $S$ and $\tau-u_a+\Theta$ in $S-[0,\Theta]\mathbf 1$. Hence
$$
\operatorname{vol}(S-[0,\Theta]\mathbf 1)=\frac{\tau^a}{a!}+\Theta\frac{\tau^{a-1}}{(a-1)!}
=\frac{\tau^a}{a!}\Bigl(1+\frac{a\Theta}{\tau}\Bigr).
$$
Since $\mathcal D=\prod_i S_i$ (slab-wise ordered simplices of the merger times),
$\mathcal D_\Theta\subset\prod_i(S_i-[0,\Theta]\mathbf 1_i)$, and with $\Theta=\tau$
the time volume is at most $\prod_i\frac{\tau^{a_i}}{a_i!}(1+a_i)\le(1+n)^L\prod_i\frac{\tau^{a_i}}{a_i!}$.
(Monte Carlo agreement for $a\le5$ is recorded in `checks/`; the identity above
is the proof.)

### 2.5 Summation over diagrams

Now repeat H's proof of `lem:sharp-factorials` and `lem:sharp-summability` on
the right side of (W1), with these modifications only.

1. *Fluxes.* H bounds the sum over chronologically ordered merger-pair choices
   of the flux products, **at fixed times, normals and birth velocities**, by
   $\prod_i(n_i^{3/2}\sqrt P)^{a_i}$. That argument uses only energy
   conservation and the fact that every redundant contact is determined by
   earlier data. Both hold for the formal history with the forward-ray rule:
   each C-update is an elastic pair reflection, whatever its time. Times enter
   only afterward, through the time volume. So the bound is unchanged.
2. *Time volume.* $\prod_i\tau^{a_i}/a_i!$ becomes at most
   $(1+n)^L\prod_i\tau^{a_i}/a_i!$.
3. *Links.* Each physical link volume $C\varepsilon^3$ becomes
   $C\varepsilon^2(\tau|u_l|+\varepsilon)$. In `eq:sharp-scaling`,
   $\mu^{c-h}\varepsilon^p$ becomes at most
   $\mu^{c-h}C^p\prod_l(1+|v_{p_l}|+|v_{q_l}|)$, with $c=1$. The extra
   $\varepsilon$ gain of a link is lost; the tree scale $\mu^{1-h}$ is kept.
   At most $2p\le2K$ velocities carry the polynomial weight. Absorbing it costs
   a factor $C_K$ and a fixed fraction of the reserved Gaussian on boundedly
   many lines. The exponential base per ordinary atom is unchanged.
4. *Marked atom.* The number of C-atoms on $\ell$ is at most the number of
   contacts, $\le n+C_K$.
5. *Fresh labels and energy bins.* Unchanged (`lem:sharp-factorials`,
   `eq:sharp-energy-sum`); they do not involve times.

The result, for slab sizes $(n_i)$, $n=\sum n_i$, is
$$
\frac{|J|}{\tau}\,C_K(1+n)^{d_K+L+1}(C\tau\sqrt L)^n\,\mu^{1-h}.
$$
With H's single choice making $CT/\sqrt L<1$, and since the number of vectors
$(n_i)$ of total $n$ is polynomial in $n$, the sum over all $n$ is
$C\mu^{1-h}|J|$. This proves Lemma W. ∎

**Why this pays the I340 obstruction.** I340 needed a free $dt$ at the marked
contact. A redundant contact has none in the chronological chart. Lemma W does
not look for one at that contact. It uses the one collective direction that
every connected history has, the simultaneous translation of all its event
times. Along that direction the marked time moves at unit speed, the measure is
invariant, and the only non-invariant data (absolute births, links, slab
membership) are handled by H's displacement-independent birth bound, a cylinder
instead of a ball, and a Minkowski enlargement. These cost polynomial factors
and the link's extra $\varepsilon$, but keep the $\mu^{1-h}$ root normalization,
the fresh-label factorials, and summability.

---

## 3. Increment cumulants and the fourth-moment bound

Fix real $\phi\in C_c^\infty$, $B=\|\phi\|_\infty$, $D_\phi=\|v\cdot\nabla_x\phi\|_\infty$.
For $0\le s<t\le T$, $\delta=t-s$, let
$S=\sum_i[\phi(\hat z_i(t))-\phi(\hat z_i(s))]$ on the pasted dynamics. This is
H's scalar mark (`eq:limit-mark-update`) with two pulses, $-\phi$ at $s$ and
$\phi$ at $t$, so $S=\sum_iy_i(T)$.

**Proposition I.** For every integer $j\ge1$ and every $P>0$ there are
constants, uniform in $s,t\in[0,T]$, with
$$
|\kappa_j(S)|\le C_j\,\mu\,\delta+C_{j,P}\,\varepsilon^P .
$$
Consequently
$$
\mathbb E|\widehat X_t(\phi)-\widehat X_s(\phi)|^4\le C(\delta^2+\delta/\mu)+C_P\varepsilon^P,
\qquad
\mathbb E|S|\le C\mu\delta+C_P\varepsilon^P. \tag{I}
$$

*Proof.* **Pointwise majorant on diagrams.** The only test used is H's own:
powers of the scalar mark $y$ of `eq:limit-mark-update` at the final time, a
function of $\xi=(x,v,y)$. The two-record function below is used only as a
pointwise bound on formal histories, never as a test of $c_h^\varepsilon$.
On a designated line with formal states $z=z_\ell(s)$ and $z'=z_\ell(t)$ the
mark is $y=\phi(z')-\phi(z)$. Put $\Phi^0_\delta(x,v)=(x+\delta v,v)$. If
$z'=\Phi^0_\delta z$, then $|y|\le D_\phi\delta$. Otherwise $|y|\le2B$. If the
line has no C-atom in $(s,t]$ then its formal state moves freely, so
$z'=\Phi^0_\delta z$. Hence, diagram-wise,
$$
|y|\le D_\phi\delta+2B\,N_{(s,t]}(\ell).
$$

**Cumulant formula.** By H `eq:limit-factorial-ordinary`,
$\kappa_j(S)=\sum_{\pi\in\mathcal P([j])}\mu^{|\pi|}\int c^\varepsilon_{|\pi|}(d\xi)\prod_{B\in\pi}y_B^{|B|}$.

**Decomposition of $c_h$, $h\le j$.** By H `thm:marked-expansion`(ii),(iii) and
§06 lines 246–255: $c_h$ equals the retained connected diagrams of complexity
$\le K$ with physical links, plus (a) diagrams with an erased initial tail,
TV $O(\varepsilon^M\mu^{1-h})$; (b) complexity $>K$, TV $\le\varepsilon^{P'}$;
(c) the variation error, TV $\le C_he^{-c\Lambda_L}$. The test is bounded by
$(2B)^j$. Choose $M,P'$ large.

**Main part.** On each retained diagram
$|\prod_By_B^{|B|}|\le(2B)^{j-1}|y_{B_1}|\le(2B)^{j-1}\bigl(D_\phi\delta+2BN_{(s,t]}(\ell_1)\bigr)$.
H's summable majorant (`lem:sharp-summability`, summed over sizes) bounds the
total absolute mass by $C\mu^{1-h}$; Lemma W bounds the $N$ term by
$C\mu^{1-h}\delta$. Multiplying by $\mu^{|\pi|}$ and summing over $\pi$ gives the
cumulant bound.

**Uniformity in $s,t$.** Lemma W and the majorant do not see pulse times.
Remainders (a)–(c) are positive history-integral dominations in which the two
pulses act only through a bounded record multiplier. (I340 analysis §6 made the
same uniformity claim; review point R2.)

**Moments.** $\mathbb E(S-\mathbb ES)^4=\kappa_4+3\kappa_2^2$ and
$\widehat X_t-\widehat X_s=\mu^{-1/2}(S-\mathbb ES)$, which gives the fourth-moment
bound after relabelling $P$. For $\mathbb E|S|$, use
$\mathbb E|S|\le\mathbb E\sum_i|y_i(T)|=\mu\int|y|\,dc_1$ (here $c_1=F_1\ge0$
and $|y|$ is a bounded function of $\xi$), then the same decomposition for
$h=1$ and the diagram-wise bound above. ∎

This replaces I340's (8). The qualitative $r^\varepsilon$ is gone: cycles,
initial links, and redundant contacts all carry the window factor $\delta$.
The only remainder is $O(\varepsilon^P)$ for arbitrary $P$, so the GRR
amplification $\alpha^{1-\gamma}$ of I340 (13) is harmless.

---

## 4. Microscopic modulus

### 4.1 Lemma E′ (flagged source reading)

Let $(i-1)\tau\le a<b\le i\tau$, so $(a,b]$ lies in slab $i$. Run the pasted
hierarchy to time $b$ with a partial final slab. Test the $h$ designated roots
by $r=\mathbf 1\{\text{the root's velocity jumps in }(a,b]\}$, a bounded
function of the root history in the final slab.

**Lemma E′.** The factorial cumulants $c_h^\varepsilon$ tested by
$\prod_kr(\ell_k)$ obey the same decomposition as in Proposition I (retained
connected diagrams, with $r$ evaluated on the designated lines' formal
histories, plus remainders (a)–(c)). The remainder constants depend only on
$h$, $P$, $M$, as for an unmarked bounded root observable.

*Justification.*
1. H `lem:autonomous-partition`, eq. `autonomous-observation`, is stated for any
   test of root histories. `lem:one-slab-expansion` is derived from it
   pointwise, and its proof uses only root-output maps and the record-free
   compatibility and acceptance indicators. Apply it in the final partial slab
   with the history test $r$; all lower slabs are unmarked.
2. Since no record is carried through a lower interface, no extra
   record-bearing line must be continued to zero beyond the designated roots,
   which H already handles. No dummy-link cost of `lem:dhm-dummies`(iii) arises
   beyond the unmarked case.
3. Every remainder bound used for (a)–(c) is a positive history-integral
   domination in which a bounded root observable "costs its supremum"
   (`thm:dhm-package`(a)).
4. In the C/O refinement of `lem:one-root-bridge` and `lem:stopped-variation`
   ("refine each autonomous C-cluster according to its complete ordered
   accepted collision history"), the root history of each diagram is its line
   with velocity jumps exactly at its C-atoms. Hence $r\le N_{(a,b]}(\ell)$
   diagram-wise.

This is the only point where the argument uses H beyond its two-pulse marks.
H's §04 text defines marks as sums of test values at pulses. It also states the
underlying identity for root-history tests. Reviewers must decide whether this
reading is acceptable (review point R3).

### 4.2 Proposition M

Let $\alpha=\alpha_\varepsilon=\mu^{-3/2}$ and
$w(Y,\lambda)=\sup_{|t-s|\le\lambda}|Y_t-Y_s|$.

**Proposition M.** $w(\widehat X(\phi),2\alpha)\to0$ in probability.

*Proof.* Let $I_k=(k\alpha,(k+3)\alpha]\cap(0,T]$, $0\le k\le\lceil T/\alpha\rceil$.
Every pair $s<t$ with $t-s\le2\alpha$ satisfies $s,t\in\overline{I_k}$ for
$k=\lfloor s/\alpha\rfloor$. Since $3\alpha<\tau$, split each $I_k$ at an
interface into at most two pieces $I_k^\iota$, each inside one slab. The
velocity path is right-continuous. A particle with no jump in $(k\alpha,t]$
moves freely, so $|\phi(\hat z(t))-\phi(\hat z(s))|\le3\alpha D_\phi$.
Otherwise the difference is at most $2B$. Summing over all particles,
$$
\sup_{s,t\in\overline{I_k}}\Bigl|\sum_i[\phi(\hat z_i(t))-\phi(\hat z_i(s))]\Bigr|
\le3\alpha D_\phi N+2B\sum_\iota\mathrm{Count}(I_k^\iota),
$$
where $\mathrm{Count}(I)=\#\{i:\text{velocity of }i\text{ jumps in }I\}=\sum_ir_i$.

*Moments of Count.* Let $F_p$ be the factorial moment measure with the test
$r$. Then $\mathbb E[\mathrm{Count}^{(p)}]=\mu^pF_p(r^{\otimes p})=\sum_{\pi}\prod_{B\in\pi}\mu^{|B|}c_{|B|}(r^{\otimes|B|})$,
the exact moment–cumulant relation for factorial measures. By Lemma E′ and
Lemma W with $J=I$, $|J|\le3\alpha$:
$|\mu^bc_b(r^{\otimes b})|\le C\mu\alpha+C_P\mu^b\varepsilon^P$.
Since $\mu\alpha=\mu^{-1/2}\le1$, every product over a partition is at most
$C_p(\mu\alpha+\mu^p\varepsilon^P)$, so
$\mathbb E[\mathrm{Count}^3]\le C(\mu\alpha+\mu^3\varepsilon^P)$.
By Markov and a union bound over at most $2(T/\alpha+2)$ pieces,
$$
P\Bigl(\max_{k,\iota}\mathrm{Count}(I_k^\iota)>\eta\sqrt\mu\Bigr)
\le\frac{C(T/\alpha)(\mu\alpha+\mu^3\varepsilon^P)}{\eta^3\mu^{3/2}}
\le C\eta^{-3}\bigl(\mu^{-1/2}+\mu^{3}\varepsilon^P\bigr)\to0
$$
for $P>6$.

*Other terms.* $\mu^{-1/2}\cdot3\alpha D_\phi N=3D_\phi\mu^{-1}(N/\mu)\to0$ in
probability, by `eq:initial-N-moments` and conservation of $N$. For the
centering, (I) gives
$\sup_{|t-s|\le2\alpha}\mu^{-1/2}|\mathbb ES_t-\mathbb ES_s|\le C\mu^{1/2}\alpha+C_P\varepsilon^P=C\mu^{-1}+o(1)$.

Combining the three bounds proves the claim. ∎

---

## 5. Chaining down to the microscopic scale

**Lemma C.** Let $Y^\varepsilon$ be càdlàg real processes on $[0,T]$ with
$Y^\varepsilon_0$ tight. Suppose that for all $s,t$,
$\mathbb E|Y_t-Y_s|^4\le C(|t-s|^2+|t-s|/\mu)+R_\varepsilon$, with
$R_\varepsilon\alpha_\varepsilon^{-2}\to0$, where $\alpha_\varepsilon=\mu^{-3/2}$,
and that $w(Y^\varepsilon,2\alpha_\varepsilon)\to0$ in probability. Then
$(Y^\varepsilon)$ is C-tight in $D([0,T])$.

*Proof.* Let $\theta=1/8$ and dyadic grids $t_{k,j}=jT2^{-k}$ for
$0\le k\le k_\varepsilon:=\max\{k:T2^{-k}\ge\alpha\}$, so that
$T2^{-k_\varepsilon}<2\alpha$. Put
$Z_k=\max_j|Y_{t_{k,j+1}}-Y_{t_{k,j}}|$. Then
$$
P(Z_k>2^{-k\theta})\le2^k\bigl[C(T^22^{-2k}+T2^{-k}\mu^{-1})+R\bigr]2^{4k\theta}.
$$
Summing over $k_0\le k\le k_\varepsilon$:
- the first term gives $C\sum_{k\ge k_0}2^{-k(1-4\theta)}$, small for large $k_0$;
- the second gives at most $C\mu^{-1}(T/\alpha)^{4\theta}=C\mu^{-1/4}\to0$;
- the third gives at most $CR(T/\alpha)^{1+4\theta}\le CR\alpha^{-2}\to0$.

On the complementary event, chaining on the finest grid gives
$|Y_u-Y_{u'}|\le Z_{k_0}+2\sum_{k>k_0}Z_k\le C_\theta2^{-k_0\theta}$ for finest-grid
points with $|u-u'|\le T2^{-k_0}$. For arbitrary $s,t$ with
$|t-s|\le T2^{-k_0-1}$, pass to adjacent finest-grid points at distance
$<2\alpha$. Hence
$w(Y,T2^{-k_0-1})\le C_\theta2^{-k_0\theta}+2w(Y,2\alpha)$. Given $\eta>0$,
choose $k_0$ and then let $\varepsilon\to0$. This verifies the C-tightness
criterion (Jacod–Shiryaev, Prop. VI.3.26; Billingsley 1999, Thm. 7.3) with the
continuous modulus. ∎

---

## 6. Proof of Theorem F

1. For each $\phi_k$, Proposition I gives the hypothesis of Lemma C for
   $\widehat X(\phi_k)$, with $R=C_P\varepsilon^P$ and $P>6$. Proposition M gives
   the microscopic hypothesis. $\widehat X_0$ is tight by H `thm:main` at $t=0$,
   together with the transfer in step 2. So each coordinate is C-tight. C-tight
   coordinates make the vector C-tight in $D([0,T],\mathbb R^m)$, because the
   continuous modulus of the vector is at most the sum of the coordinate moduli.
2. *Transfer* (I340 §3, credited). On the coupling of H `prop:cutoff`, with
   event $E^\varepsilon$, $\sup_t|S_t-\widehat S_t|\le2\|\phi\|_\infty N\mathbf 1_{E^\varepsilon}$.
   Hölder with $p=22$ and `eq:initial-N-moments` give
   $\sup_t|\mathbb ES_t-\mathbb E\widehat S_t|/\sqrt\mu\le C\varepsilon^{1/440}$.
   Hence $\|X^\varepsilon-\widehat X^\varepsilon\|_\infty\to0$ in probability.
   Since $w(X,\lambda)\le w(\widehat X,\lambda)+2\|X-\widehat X\|_\infty$, the true
   vector is C-tight.
3. *Identification.* Every subsequential limit is supported on $C$. Its
   finite-dimensional laws are those of $\zeta$ at all times, by H `thm:main`
   (joint, for all finite lists of times and tests). Finite-dimensional laws
   determine a law on $C$. The continuous version of $\zeta$ exists (I340 §2).
   So the whole sequence converges, in $J_1$ and in the uniform topology. ∎

---

## 7. Checks a reviewer should make

- **R1 (Lemma W core).** Check that $F_G\le F^{\rm ext}_G$ pointwise; that
  dropping lifetime, segment and chronology constraints is harmless for H's
  discrete flux-tree argument; and that H's link coordinates are relative affine
  origins at time $0$ (H §06 lines 168–173).
- **R2 (pulse-time uniformity).** Remainders (a)–(c) of
  `thm:marked-expansion` are uniform in pulse times for a fixed number of
  pulses. This was already used in I340 §6.
- **R3 (Lemma E′).** Final-slab root-history tests (§4.1).
- **R4.** The Gaussian absorption of $\prod(1+|u_l|)$ over at most $2K$ lines
  does not change the per-atom base.
- **R5.** The moment–cumulant relation for factorial measures with records, and
  H `eq:limit-factorial-ordinary` applied to the two-pulse mark.
- **R6.** In Lemma C, the arithmetic for $\alpha=\mu^{-3/2}$, $\theta=1/8$:
  $\mu^{-1}\alpha^{-1/2}=\mu^{-1/4}$ and $R\alpha^{-3/2}\le\varepsilon^{P-9/2}$.

## 8. Contribution limits

- Theorem F would extend BGSS's nonequilibrium functional theorem
  (arXiv:2008.10403v2, short times, torus) to the full DHM-regular lifespan in
  the whole space, relative to H. That comparison is from I340's reading and
  has not been redone here.
- The GRR/chaining and transfer machinery is credited old machinery (BGSS;
  I340 parent).
- The new ingredient is Lemma W. Whether whole-history time-translation
  averaging already appears in the BGSS cumulant papers or elsewhere has
  **not** been checked. A separate primary-literature contribution review must
  decide novelty.
- Formal support: none yet. A Lean statement of the Minkowski-volume identity
  and of the averaging inequality for translation-covariant event times would
  be a natural supporting lemma. It would not formalize the theorem.
