# Candidate: a fixed power-law violation of Yau's nodal upper bound in dimension four

Author: Myeongjin Kang (no affiliation). Original prose: CC BY 4.0.

Status: **PROOF-CANDIDATE**. Not self-passed, not counted. Campaign count
is unchanged (4/10); only the parent integrates. Integrity checks in this
directory do not establish the mathematics or its novelty.

Frozen scope: `original-scope.md`, SHA256
`3348c130c424d6f753a39c6529cff81c0d923c3bb8d1eeb395327abb6734dc0f`
(frozen 2026-10-16T14:37:52Z, before the proof below was written).

---

## 0. The result

**Theorem T4.** There exist a smooth Riemannian metric $g$ on the closed
connected four-manifold $S^3\times S^1$, a number $\epsilon_0>0$, and
nonzero real smooth functions $u_j$ with positive numbers $\lambda_j$ such
that

$$
-\Delta_g u_j=\lambda_j u_j,\qquad \lambda_j\to\infty,\qquad
\frac{\mathcal H^3_g(Z(u_j))}{\lambda_j^{1/2+\epsilon_0}}\to\infty .
$$

The metric and $\epsilon_0$ are fixed along the sequence. Here $Z(u)$ is
the zero set and $\mathcal H^3_g$ is three-dimensional Hausdorff measure
of the Riemannian distance.

So the smooth upper-bound half of Yau's conjecture fails in dimension four
with a fixed power loss. Products with a fixed closed manifold then give
the same in every dimension $n\ge4$; dimensions $n\ge5$ were already in
the pinned source [P].

**What is new relative to the pinned sources.** [P] proves the same
statement on $S^4\times S^1$ and says (introduction, lines 46–48) that it
makes no assertion in dimensions three or four. [Q] proves unbounded
$\mathcal H^{n-1}(Z)/\sqrt\lambda$ in dimensions three and four without a
fixed power. [P] names the single place where base dimension four is used
(envelopes.tex lines 432–433, end of the proof of `lem:corrugation`).
This candidate replaces that step by a quantitative, fixed-scale-ratio
envelope amplification on a three-dimensional base (Sections 3–8), then
runs the rest of [P] on the base $S^3$ (Section 9).

### Sources

* [P] = `preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026`
  (framework.tex, envelopes.tex, waves.tex, global.tex, introduction.tex).
* [Q] = `preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026`
  (introduction.tex, s3-profiles.tex, s4-envelopes.tex).

Both are at openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; Git
blob identities are in `git-identities.json` and `source-contracts.md`.
Their theorems are accepted as true. [P]'s lemmas are proved for the base
$B=S^4$. Their base-$S^3$ analogues are **not** upstream theorems; they
are new deductions here, justified by the itemized transfer in Section 9.

---

## 1. Architecture

[P] proves its Theorem 1.1 in three layers.

1. `prop:envelope` (envelopes.tex): a smooth envelope $h=h_k$ on the base
   with $\|h\|_{C^j}\le C_jk^{\delta(j+1)}$, a Hessian-test margin
   $\ge ck^{-\delta}$ on $\{t\ge1/4\}$, and
   $\int_V\sqrt{1+|\nabla h|^2}\ge ck^\gamma$, with $\gamma>0$ fixed.
2. Packets under $e^{kh}$, a Gaussian sample with a nonvanishing first jet
   and a sign certificate of size $\ge ck^{1+\gamma}$, exact correction of
   the weighted pair, simplicity, and persistence (`prop:step`).
3. A summable iteration to one smooth pair, then a warped circle that turns
   the weighted operator into a Laplace–Beltrami operator.

Layers 2 and 3 use only the conclusions of `prop:envelope`. The proof of
`prop:envelope` uses base dimension four exactly once: in
`lem:corrugation` an old favorable two-plane $RE$ and the new favorable
plane $\mathcal F$ lie in the three-dimensional $\ker\mathrm dv$ and meet
in dimension $2+2-3=1$. On a three-dimensional base, $\ker\mathrm dv$ is a
plane and the new favorable set $\mathcal F$ is a line. Then [P]'s
preparation condition, a two-plane inside $\ker\mathrm dh$, means that
the **whole** kernel is favorable. Radial wells in two transverse
variables produce only one favorable line on their repeat region, so [P]'s
corrugation cannot be iterated as stated.

The fix is to alternate two operations with a fixed scale ratio.

* **Fullification (Lemma 6.1, new).** From one favorable direction at
  scale $S$, make the whole kernel favorable at the same scale $S$ on a
  set carrying a fraction $1-2\kappa$ of the mass, for any fixed
  $\kappa>0$. Gradients change only by a factor $1\pm\nu$.
* **Radial corrugation with full input (Lemma 5.1).** This is [P]'s
  corrugation, with $E=\ker\mathrm dh$. On a three-dimensional base the
  intersection count becomes $2+1-2=1$. It gains mass by a factor
  $1+\zeta_B$ and outputs one favorable direction at the finer scale.

Choosing $\kappa$ after $\zeta_B$ makes one generation gain a fixed
factor $1+\zeta_B/2$ (Lemma 7.1). All constants are ordered so that the
scale ratio per generation, $r=\nu^6$, is fixed. The iteration then gives
the three-dimensional `prop:envelope` with the same exponents
(Proposition 8.1).

---

## 2. Setting and notation

$B=S^3\subset\mathbb R^4$ with round metric $g_0$ and density $\mu$. A
point is $(x_1,x_2,y)$ with $y\in\mathbb R^2$, and $t=|y|^2$. Positive
pairs $(A,\rho)$, the metric $G$ with $G^{-1}=\rho^{-1}A$, and
$Lf=\rho^{-1}\mathrm{div}_\mu(A\,\mathrm df)$ are as in [P, framework,
eq:weighted-operator]. For a smooth real $h$,

$$
p=\nabla_Gh,\quad Q=(1+|p|_G^2)^{1/2},\quad D_h=p/Q,\quad
J_h(e)=\nabla^2_Gh(D_h,D_h)+\nabla_G^2h(e,e),
$$

for $|e|_G=1$ and $\mathrm dh(e)=0$; if $p=0$ every unit $e$ is allowed
([P, eq:hessian-test]).

Fix a coordinate chart $\Omega\subset\{t>1/2\}$ with coordinates
$x\in\mathbb R^3$, defined near $\overline\Omega$. The **metric class**
$\mathcal G_\Lambda$ consists of smooth metrics with
$\Lambda^{-1}I\le(G_{ij})\le\Lambda I$ and $|DG|\le\Lambda$ on
$\overline\Omega$. Only these $C^1$ bounds enter the envelope constants.
$D$ denotes coordinate derivatives with Euclidean norms; $\nabla$,
$\nabla^2$ refer to $G$. Christoffel symbols are bounded by $C_\Gamma(\Lambda)$,
so

$$
|\nabla^2h-D^2h|\le C_\Gamma|\mathrm dh| . \tag{2.1}
$$

**Normalized-gradient stability** ([P, eq:normalized-gradient-stability]).
For $T(p)=p/\sqrt{1+|p|^2}$, if $|q-p|\le\varepsilon|p|$ and
$\varepsilon\le1/2$, then $|T(q)-T(p)|\le2\varepsilon$. (The segment
from $p$ to $q$ avoids the ball of radius $|p|/2$, and
$|DT(\xi)|\le(1+|\xi|^2)^{-1/2}$.)

**Definition 2.1 (preparation).** Let $P\subset\Omega$ be a closed
coordinate cube and $0<S\le1$. All inequalities are required at every
point of $P$.

* (W) $h$ is **weakly prepared at scale $S$ with constants $(C,c)$** if
  $|\nabla h|>0$, $|D^2h|\le C|\nabla h|/S$, $|D^3h|\le C|\nabla h|/S^2$,
  and some $G$-unit $e\in\ker\mathrm dh$ has $J_h(e)\ge c|\nabla h|/S$.
* (F) $h$ is **fully prepared at scale $S$ with constants $(C,c)$** if
  $|\nabla h|>0$, $|D^2h|\le C|\nabla h|/S$, and **every** $G$-unit
  $e\in\ker\mathrm dh$ has $J_h(e)\ge c|\nabla h|/S$.

The favorable direction in (W) need not vary continuously. On a
three-dimensional base, (F) is exactly [P]'s condition (eq:preparation)
with $E=\ker\mathrm dh$. The third-derivative bound in (W) is used only
in Lemma 6.1, to carry a favorable direction across a cube.

**Mass.** For a set $U$ and function $h$, $M(U,h)=\int_U|\nabla h|_G\,\mathrm dx$.

---

## 3. Seed on $S^3$

**Lemma 3.1.** There are $a_*>0$, a smooth $h_0$ on $B$, a $C^1$
neighborhood $\mathcal G$ of $g_0$, a chart $\Omega\subset\{t>1/2\}$, and
open $U_0\Subset V\Subset\Omega$ such that, uniformly for $G\in\mathcal G$:

1. $h_0=-a_*t$ on $\{t\le1/2\}$;
2. $\max_eJ_{h_0}(e)\ge c_0>0$ on $\{t\ge1/4\}$ (all admissible tests);
3. on $\overline{U_0}$, $\nabla_G^2h_0\ge\lambda_0G$ with $\lambda_0>0$, and
   $0<s_{\min}\le|\nabla h_0|\le s_{\max}$.

Consequently there are $(C_0,c_0')$ such that every closed cube in
$\overline{U_0}$ is fully prepared for $h_0$ at scale $1$ with constants
$(C_0,c_0')$, and $|D^3h_0|\le C_0|\nabla h_0|$ there.

*Proof.* This is [P, lem:seed] with the dimension changed; the changed
facts are checked here. For $\tilde h=-a_*t$, the restriction formula
$\nabla^2_{S}(f|_S)=(D^2_{\mathbb R^4}f)|_T-(\partial_rf)g_0$ with
$f=-a_*|y|^2$ and $\partial_rf=-2a_*t$ gives

$$
|\nabla_{g_0}\tilde h|^2=4a_*^2t(1-t),\qquad
\nabla^2_{g_0}\tilde h=2a_*(tg_0-\mathrm dy\cdot\mathrm dy).
$$

The map $\mathrm dy:T_xS^3\to\mathbb R^2$ has a three-dimensional domain,
so it has a unit kernel vector $e$. Then $\mathrm d\tilde h(e)=0$ and
$\nabla^2\tilde h(e,e)=2a_*t$. Also $|\nabla^2\tilde h|\le2a_*$ and
$|D_{\tilde h}|^2\le|p|^2\le a_*^2$, so on $t\ge1/4$,
$J_{\tilde h}(e)\ge a_*/2-2a_*^3\ge a_*/4$ when $a_*^2\le1/8$.

At $x_*=(0,0,y_*)$ with $|y_*|=1$ the gradient vanishes. The tangent
space is $\mathbb R^2_{x_1x_2}\oplus y_*^\perp$, and the Hessian there has
eigenvalues $2a_*,2a_*,0$. Add $\varepsilon|\xi|^2/2$ times a fixed
cutoff in normal coordinates $\xi$ at $x_*$, with $\varepsilon$ and the
support small. On the support, the Hessian keeps a two-plane with
eigenvalues $\ge ca_*$, its norm is $\le Ca_*$, and $|\nabla h_0|$ is so
small that $Ca_*|\nabla h_0|^2<ca_*/2$. A positive two-plane in the
three-dimensional tangent space meets the plane $\ker\mathrm dh_0$ (or
equals any plane if $\mathrm dh_0=0$) in dimension $\ge1$. A unit vector
there gives $J_{h_0}\ge ca_*/2$. Outside the support the $\ker\mathrm dy$
test applies. Persistence under $C^1$-small metric changes is as in [P]:
Hessians of a fixed function differ by the connection difference
contracted with $\mathrm dh_0$, and $\mathrm dy(e)=0$ implies
$\mathrm dh_0(e)=0$ for every metric. At $x_*$ the new Hessian is
positive definite, so it stays positive definite on a neighborhood. That
neighborhood contains a point with $\mathrm dh_0\ne0$, since otherwise
$h_0$ would be locally constant. Take $U_0$ to be a small neighborhood of
that point, and choose $\Omega,V$ and shrink $\mathcal G$.

For the consequence: if $\nabla^2h_0\ge\lambda_0G$, then for every unit
$e\in\ker\mathrm dh_0$,
$J_{h_0}(e)\ge\lambda_0(|D_{h_0}|^2+1)\ge\lambda_0\ge(\lambda_0/s_{\max})|\nabla h_0|$.
The derivative bounds hold on the compact set $\overline{U_0}$ because
$|\nabla h_0|\ge s_{\min}$. $\square$

---

## 4. Fixed choices for the transverse pattern

These data depend only on absolute choices (not on $\Lambda$, nor on any
preparation constant).

* $F\in C^\infty[0,1]$ is positive on $(0,1)$, equals $v$ near $0$, and is
  flat at $1$.
* The amplitude $a\in(0,1]$ satisfies
  $a^2\sup_{v}vF(v)|F'(v)|\le1/32$.
* On the unit square cell of $\mathbb R^2$, take finitely many closed
  disks with disjoint closures and radii $R_i\in[R_{\min},1]$. On each
  disk, at radius $r$ from its center, set
  $\psi(r)=-\int_r^{R_i}F(q/R_i)\,\mathrm dq$, $f(r)=F(r/R_i)$,
  $u_0=f/r$. Extend by $0$ and $\mathbb Z^2$-periodically. Then $\psi$ is
  smooth, and with radial unit vector $\sigma$,

  $$
  \nabla\psi=f\sigma,\quad D^2\psi=f'\sigma\otimes\sigma+u_0(I-\sigma\otimes\sigma),\quad
  f^2|f'|=vF|F'|\,u_0,\quad f^2\le u_0 . \tag{4.1}
  $$

  (Here $v=r/R_i$, $f^2/u_0=R_ivF\le1$ after normalizing
  $\sup F\le1$, and $u_0=0\Rightarrow f=f'=\psi=0$.)
* $\mathcal W(a)=2\int_0^1v\sqrt{1+a^2F(v)^2}\,\mathrm dv>1$ is the mean
  gradient factor on one disk. Put $\eta_0=(\mathcal W(a)-1)/8$. The
  packing has area fraction $\varpi$ with $\varpi\mathcal W(a)>1+6\eta_0$.
  Such a finite packing exists by the repeated-grid argument in [P,
  envelopes.tex lines 227–233]: each round of grid squares with inscribed
  smaller disks captures a fixed fraction of the remaining area.
* $\eta\in(0,1)$ makes the core integral
  $C_{\rm core}=\sum_i\int_{r\le(1-\eta)R_i}\sqrt{1+a^2f^2}\,\mathrm dz'>1+5\eta_0$.
  On the cores, $u_0\ge u_{\min}>0$.
* $q\in(0,1)$ satisfies $qC_{\rm core}>1+4\eta_0$. The cutoff $\chi$ on
  the unit cube of $\mathbb R^3$ is a product of one-dimensional plateau
  cutoffs. It equals $1$ on the concentric inner cube of volume fraction
  $q$, is supported in the interior, and is flat on its zero set.

Set $\zeta_B=\eta_0/(1+\eta_0)$ and $c_a=a/4$.

---

## 5. Radial corrugation with full input

**Lemma 5.1.** There are constants $\lambda_0\in(0,1)$, $c_\flat>0$,
$C_\flat$, $C^\flat_j$ ($j\ge0$), $\alpha_B=1/2$, $\beta_B=2\sqrt{1+a^2}$,
depending only on $\Lambda$ and Section 4, with the following property.
For all $C\ge1$ and $c\in(0,1]$ there is $\mu_0=\mu_0(C,c,\Lambda)>0$.
Let $\lambda\le\lambda_0$ and $\mu\le\mu_0$ be reciprocal integers, let
$Q\subset\Omega$ be a closed cube of side $\mu S$ with $0<S\le1$, and let
$h$ be fully prepared on $Q$ at scale $S$ with constants $(C,c)$. Put
$\ell=\mu^2S$ and $s=|\nabla h(x_Q)|$ at the center $x_Q$. Then
$v=h+w$, with $w$ smooth and supported in $\operatorname{int}Q$, satisfies:

1. $\alpha_B|\nabla h|\le|\nabla v|\le\beta_B|\nabla h|$ and
   $\max_eJ_v(e)\ge(c/16)|\nabla h|/S$ on $Q$;
2. let $\mathcal R_Q$ be the union of the closed cubes of side
   $\lambda\ell$ in the exact partition of $Q$ that lie in the repeat
   region defined below. On $\mathcal R_Q$, $v$ satisfies
   $|D^2v|\le C_\flat|\nabla v|/\ell$, some unit $e\in\ker\mathrm dv$ has
   $J_v(e)\ge c_\flat|\nabla v|/\ell$, and
   $|D^3v|\le C_\flat|\nabla v|/\ell^2+|D^3h|$. Moreover
   $M(\mathcal R_Q,v)\ge(1+\zeta_B)M(Q,h)$;
3. $\|D^jw\|_{L^\infty}\le C^\flat_js\ell^{1-j}$ for every $j\ge0$.

*Proof.* The proof follows [P, lem:corrugation] line by line, with three
transverse variables replaced by two. The parent two-plane $E$ is
replaced by the full kernel. We write out every step that changes.

*Normalization.* Take affine coordinates $z=(z_1,z')$, $z'=(z_2,z_3)$,
centered at $x_Q$, with $G(x_Q)=I$ and $\nabla h(x_Q)=s\partial_{z_1}$.
The affine maps and their inverses are bounded in terms of $\Lambda$. By
(2.1) and (F), $|D(\mathrm dh)|\le C'|\mathrm dh|/S$ with
$C'=C(C+C_\Gamma)$. Integrating along segments of length $O(\mu S)$ gives

$$
\mathrm dh/s=\mathrm dz_1+O(\mu),\qquad G=I+O(\mu S),\qquad
|\nabla h|/s=1+O(\mu). \tag{5.1}
$$

Rescale $\chi$ to $Q$ in the original coordinates and set

$$
v=h+s\ell a\chi\,\psi(z'/\ell),\qquad \ell=\mu^2S . \tag{5.2}
$$

Radial coefficients are evaluated at $z'/\ell$, and $D_{\rm sc}\chi$
denotes cutoff derivatives at the parent scale, so
$|D\chi|=(\mu S)^{-1}|D_{\rm sc}\chi|$. Since $\ell/(\mu S)=\mu$,
$\mathrm dv/s=\mathrm dz_1+a\chi f\sigma\cdot\mathrm dz'+O(\mu)$. This
gives the gradient comparison in (1) for $\mu$ small, because
$1\le\sqrt{1+a^2\chi^2f^2}\le\sqrt{1+a^2}$.

*Favorable line.* Let
$\mathcal F=\{e:\mathrm dv(e)=0,\ \sigma\cdot e'=0\}$. The two conditions
are independent, so $\mathcal F$ is a **line**. For a $G$-unit
$e\in\mathcal F$, the first condition gives
$e_1=-a\chi f\sigma\cdot e'+O(\mu)=O(\mu)$. Hence
$|e'|^2\ge1/2$. Since $|\nabla v|\ge s/2$,

$$
|\sigma\cdot D_v'|\le2a\chi f+C\mu,\qquad
(\sigma\cdot D_v')^2\le8a^2\chi^2f^2+C\mu^2 . \tag{5.3}
$$

*New Hessian.* Divided by $s/\ell$,
$D^2(v-h)=a\chi D^2\psi+a\mu(D_{\rm sc}\chi\otimes f\sigma+f\sigma\otimes D_{\rm sc}\chi)+a\mu^2\psi D^2_{\rm sc}\chi$.
By (4.1), the leading part evaluated on $(D_v,D_v)+(e,e)$ is

$$
a\chi\bigl[f'(\sigma\cdot D_v')^2+u_0(|\Pi_\sigma D_v'|^2+|e'|^2)\bigr]
\ge a\chi\bigl[\tfrac12u_0-|f'|(8a^2\chi^2f^2+C\mu^2)\bigr]
\ge\tfrac14a\chi u_0-Ca\mu^2\chi|f'| ,
$$

because $8a^2f^2|f'|=8a^2vF|F'|u_0\le u_0/4$ by the amplitude choice. The
mixed cutoff terms vanish on $(e,e)$ because $\sigma\cdot e'=0$. On
$(D_v,D_v)$ they are at most $C\mu f|D_{\rm sc}\chi|(\chi f+\mu)$. Pure
cutoff terms are at most $C\mu^2|\psi||D^2_{\rm sc}\chi|$. Replacing
$D^2$ by $\nabla^2$ costs $|\Gamma||\mathrm d(v-h)|\cdot\ell/s\le C\ell(\chi f+\mu)$.

Put $X=\chi u_0$. On a compact parameter space (cutoff position, period
position, bounded affine frames), continuous $X,b\ge0$ with $b=0$ on
$\{X=0\}$ satisfy $\sup\mu^2b/(X+\mu^2)\to0$ as $\mu\to0$ ([P,
eq:vanishing-coefficient]: split at $X\ge\tau$ and $X<\tau$). Apply this
to $b=\chi|f'|$, $f|D_{\rm sc}\chi|$, and $|\psi||D^2_{\rm sc}\chi|$.
These vanish where $X=0$ by (4.1) and because $\chi$ is flat where it
vanishes. Further, $\mu\chi f^2|D_{\rm sc}\chi|\le C\mu X$ by
$f^2\le u_0$. Also $\chi f\le\sqrt X$ (since $\chi^2f^2\le\chi u_0$) and
$\ell\le\mu^2$, so
$\ell(\chi f+\mu)/(X+\mu^2)\le\mu^2\sqrt X/(X+\mu^2)+\mu\le2\mu$.
Hence, for every unit $e\in\mathcal F$,

$$
\frac{\ell}{s}\bigl[\nabla^2(v-h)(D_v,D_v)+\nabla^2(v-h)(e,e)\bigr]
\ge c_aX-\varepsilon(\mu)(X+\mu^2),\qquad\varepsilon(\mu)\to0 . \tag{5.4}
$$

The function $\varepsilon$ depends only on $\Lambda$ and Section 4.

*Retaining one direction everywhere (the changed step).* By (2.1) and
(F), $(\ell/s)|\nabla^2h|\le C''\mu^2$ with $C''=2(C+C_\Gamma)$. Write
$J_v(e)=[\nabla^2h(D_v,D_v)+\nabla^2h(e,e)]+[\text{(5.4) terms}]$ for
$e\in\mathcal F$. Suppose the margin $c\mu^2/8$ (normalized units) fails
along a sequence $\mu_n\to0$ of admissible configurations. Pass to a
subsequence.

* If $X/\mu^2\to\infty$, then
  $(\ell/s)J_v(e)\ge c_aX-\varepsilon(X+\mu^2)-2C''\mu^2\ge c_aX/2-3C''\mu^2$,
  which eventually exceeds $c\mu^2/8$.
* If $X\le K\mu^2$, then $\chi f\le\sqrt K\mu$. So
  $|\nabla v-\nabla h|\le\varepsilon_1|\nabla h|$ with
  $\varepsilon_1\le C(\sqrt K+1)\mu$. There is a $G$-orthogonal map
  $R=I+O(\varepsilon_1)$ taking the plane $\ker\mathrm dh$ to the plane
  $\ker\mathrm dv$. For unit $e\in\mathcal F\subset\ker\mathrm dv$, the
  vector $R^{-1}e$ is a unit vector of $\ker\mathrm dh$. By **full**
  preparation, $(\ell/s)J_h(R^{-1}e)\ge c\mu^2(1-C\mu)$. By the stability
  of $T$, $|D_v-D_h|\le2\varepsilon_1$. So the old bracket differs from
  $(\ell/s)J_h(R^{-1}e)$ by at most
  $C''\mu^2\cdot C\varepsilon_1=O(\mu^3)$. The new bracket is
  $\ge-\varepsilon(\mu)(K+1)\mu^2$. The total is $\ge c\mu^2/2$
  eventually.

Both cases contradict failure. So for $\mu\le\mu_0(C,c,\Lambda)$ every
point of $Q$ has a unit $e\in\mathcal F$ with
$J_v(e)\ge(c/8)s/S\ge(c/16)|\nabla h|/S$. This is (1). In [P] this step
needed $\dim(RE\cap\mathcal F)\ge2+2-3$. Here $RE=\ker\mathrm dv$ and
$\mathcal F\subset\ker\mathrm dv$, so the intersection is $\mathcal F$
itself.

*Repeat region.* Let the repeat region be the closed set where $\chi=1$
and $z'/\ell$ lies (mod $\mathbb Z^2$) in a closed core disk
$r\le(1-\eta)R_i$. There $X=u_0\ge u_{\min}$. By (5.4),
$(\ell/s)J_v(e)\ge c_au_{\min}-\varepsilon(\mu)(1+\mu^2)-2C''\mu^2\ge c_au_{\min}/2$
for $e\in\mathcal F$ and $\mu$ small. Also
$|D^2v|\le|D^2h|+|D^2w|\le(C\mu^2\cdot2+C^\flat_2)s/\ell$ and
$|D^3v|\le|D^3h|+C^\flat_3s/\ell^2$. Since $|\nabla v|\ge s/2$ there, we
can take $c_\flat=c_au_{\min}/(4\beta_B)$ and
$C_\flat=4\max(C^\flat_2,C^\flat_3)+1$, for $\mu\le\mu_0(C,c,\Lambda)$.
These two constants depend only on $\Lambda$ and Section 4.

*Mass.* $\lambda,\mu$ are reciprocal integers, so $Q$ (side $\mu S$) is
exactly partitioned into cubes of side $\lambda\ell=\lambda\mu^2S$. On the
repeat region $|\nabla v|/s=\sqrt{1+a^2f^2}+O(\mu)$. Tile the affine
coordinates by period cells of side $\ell$, with a dummy period in $z_1$.
Cells meeting the inner-cube boundary have relative volume
$O(\ell/(\mu S))=O(\mu)$. Discarding child cubes that meet the boundaries
of the cores or of the inner cube loses a layer of width $O(\lambda\ell)$.
The cores have boundaries of finite length per period, so the relative
loss is $C_{\rm pat}\lambda$, with $C_{\rm pat}$ depending on Section 4
(including $R_{\min}$). Hence

$$
\frac{M(\mathcal R_Q,v)}{s|Q|}\ge qC_{\rm core}-C_{\rm pat}\lambda-C\mu,
\qquad\frac{M(Q,h)}{s|Q|}\le1+C\mu .
$$

Choose $\lambda_0$ with $C_{\rm pat}\lambda_0\le\eta_0/2$, and shrink
$\mu_0$ so that the remaining errors are $\le\eta_0/2$. Then the ratio
exceeds $(1+3\eta_0)/(1+\eta_0)\ge1+\zeta_B$.

*Derivatives.* A term of $D^j$ of (5.2) with $m$ derivatives on $\chi$
has size $s\ell(\mu S)^{-m}\ell^{-(j-m)}=s\ell^{1-j}\mu^m$. The pattern
derivatives and affine matrices enter $C^\flat_j$. $\square$

---

## 6. Fullification at a fixed scale (new step)

**The one-dimensional profile.** Fix $\kappa\in(0,1/4)$. Let
$\mathbf E=[0,1-\kappa]+\mathbb Z$. Choose a smooth bump $\beta_\kappa\ge0$
supported in $(1-\kappa,1)$ with $\int\beta_\kappa=1$. Put
$\phi=1-\beta_\kappa$, extended 1-periodically. Then $\int_0^1\phi=0$ and
$\phi=1$ on $\mathbf E$. Let $H'(t)=\int_0^t\phi-m_\kappa$, where
$m_\kappa$ makes $H'$ of mean zero, and let $H(t)=\int_0^tH'$. Then $H$
is smooth and 1-periodic, and $H''=\phi\ge1$ on $\mathbf E$. Write
$\mathsf h_j=\sup|H^{(j)}|$; these depend only on $\kappa$.

**The cutoff.** $\chi_A$ is a product of one-dimensional plateau cutoffs
on the unit cube. It equals $1$ on the concentric inner cube of volume
fraction $1-\kappa$, is supported in the interior, and is flat on its zero
set. All derivatives of $\chi_A$ vanish on the closed set
$\{\chi_A=1\}$, by continuity from its interior.

**Lemma 6.1.** Let $C_B\ge1$, $c_B\in(0,1]$, and $\kappa\in(0,1/4)$. There
are $b=b(C_B,c_B,\Lambda)$ (independent of $\kappa$),
$C_A=C_A(C_B,c_B,\kappa,\Lambda)$, $c_A=c_B/8$, constants
$C^A_j(C_B,c_B,\kappa,\Lambda)$, and $\nu_A=\nu_A(C_B,c_B,\kappa,\Lambda)>0$
with the following property. Let $\nu\le\nu_A$ be a reciprocal integer,
let $0<S\le\nu$, and let $h$ be weakly prepared at scale $S$ with
constants $(C_B,c_B)$ on a closed cube $P\subset\Omega$ of side $\nu S$.
Put $s=|\nabla h(x_P)|$ and $\ell_A=\nu^2S$. Then there is
$v_A=h+w_A$, with $w_A$ smooth and supported in $\operatorname{int}P$,
such that:

* (a) $(1-\nu)|\nabla h|\le|\nabla v_A|\le(1+\nu)|\nabla h|$ on $P$;
* (b) $\|D^jw_A\|_{L^\infty}\le C^A_jbs\nu^{4-2j}S^{1-j}$;
* (c) $\max_eJ_{v_A}(e)\ge(c_B/4)|\nabla h|/S$ on $P$;
* (d) on the closed set
  $\mathcal A=\{x\in P:\chi_A(x)=1,\ z_3(x)/\ell_A\in\mathbf E\}$, $v_A$
  is fully prepared at scale $S$ with constants $(C_A,c_A)$;
* (e) $|D^3v_A|\le(4C_B+C^A_3b\nu^{-2})s/S^2$ on $P$;
* (f) the union $\mathcal A^\sharp$ of the closed cubes of side $\nu^3S$
  of the exact partition of $P$ that lie in $\mathcal A$ satisfies
  $|\mathcal A^\sharp|\ge(1-2\kappa-C_\kappa\nu)|P|$, with $C_\kappa$
  depending on $\kappa,\Lambda$.

Here $z$ are the frozen coordinates defined in the proof.

*Proof.* *Frozen frame.* By (W) at $x_P$, choose a $G$-unit
$e_*\in\ker\mathrm dh(x_P)$ with $J_h(x_P;e_*)\ge c_B s/S$. Take affine
coordinates $z$ centered at $x_P$ with $G(x_P)=I$,
$\nabla h(x_P)=s\partial_{z_1}$ and $\partial_{z_2}=e_*$. The map and its
inverse are bounded by $\Lambda$. As in (5.1), with $\omega=C(C_B+C_\Gamma)\nu$,

$$
\mathrm dh/s=\mathrm dz_1+O(\omega),\qquad G=I+O(\nu S),\qquad
|\nabla h|/s=1+O(\omega)\quad\text{on }P . \tag{6.1}
$$

*The perturbation.* Rescale $\chi_A$ to $P$ (original coordinates; so
$|D^m\chi_A|\le C_m(\nu S)^{-m}$) and set

$$
w_A=b\,\frac{s}{S}\,\ell_A^2\,\chi_A\,H(z_3/\ell_A),\qquad v_A=h+w_A .
$$

Direct differentiation gives

$$
\begin{aligned}
\mathrm dw_A&=bs\nu^2\chi_AH'\,\mathrm dz_3+bs\nu^4SH\,\mathrm d\chi_A,\\
D^2w_A&=b\frac sS\chi_AH''\,\mathrm dz_3\otimes\mathrm dz_3
+bs\nu^2H'(\mathrm d\chi_A\otimes\mathrm dz_3+\mathrm dz_3\otimes\mathrm d\chi_A)
+bs\nu^4SH\,D^2\chi_A .
\end{aligned}
$$

So $|\mathrm dw_A|\le Cbs\nu^2$, and

$$
\nabla^2w_A=b\frac sS\chi_AH''\,\mathrm dz_3^{\otimes2}+\mathcal E_A,\qquad
|\mathcal E_A|\le Cb\nu\,\frac sS, \tag{6.2}
$$

where the Christoffel term is $\le C|\mathrm dw_A|\le Cbs\nu^2\le Cb\nu^2s/S$.
On $\{\chi_A=1\}$ all cutoff terms vanish, and
$|\mathcal E_A|\le Cb\nu^2s/S$ there. Item (a) follows from (6.1) once
$Cb\nu^2\le\nu/2$. Item (b) is the same scale count as in Lemma 5.1. Item
(e) follows from (W) and $|D^3w_A|\le Cbs/(S\ell_A)$.

*The transported favorable direction.* At $x\in P$ let $e_2(x)$ be a
$G(x)$-unit vector spanning the line $\ker\mathrm dv_A\cap\ker\mathrm dz_3$.
The two covectors are independent because
$\mathrm dv_A/s=\mathrm dz_1+O(\omega+b\nu^2)$. Then
$e_2=\pm\partial_{z_2}+O(\omega+b\nu^2+\nu S)$. We compare the old part
of $J_{v_A}(e_2)$ at $x$ with $J_h(x_P;e_*)$.

* Coordinate Hessians: $|D^2h(x)-D^2h(x_P)|\le|D^3h|\cdot C\nu S\le CC_B\nu s/S$,
  by the third-derivative bound in (W).
* Christoffel parts: $|\Gamma(x)\mathrm dh(x)|+|\Gamma(x_P)\mathrm dh(x_P)|\le Cs=CS\cdot s/S\le C\nu s/S$,
  using $S\le\nu$. Only $C^0$ bounds on $\Gamma$ are used.
* Vectors: $|D_{v_A}(x)-D_h(x_P)|\le C(\omega+b\nu^2+\nu S)$ by
  normalized-gradient stability, and
  $|e_2-\partial_{z_2}|\le C(\omega+b\nu^2+\nu S)$.

With $|\nabla^2h|\le2(C_B+C_\Gamma)s/S$, the old bracket
$\nabla^2h(D_{v_A},D_{v_A})+\nabla^2h(e_2,e_2)$ at $x$ is at least
$[c_B-C(C_B+1)^2\nu-C(C_B+1)b\nu^2]\,s/S$.

For the added part, $\mathrm dz_3(e_2)=0$ kills the leading term on
$(e_2,e_2)$. On $(D_{v_A},D_{v_A})$, the $z_3$-component of
$\nabla_Gv_A$ is $O(\omega+b\nu^2+\nu S)s$ by (6.1) and the formula for
$\mathrm dw_A$. Since $Q\ge|\nabla v_A|\ge s/2$, this gives
$|\mathrm dz_3(D_{v_A})|\le C(\omega+b\nu^2)$. Hence, by (6.2),

$$
|\nabla^2w_A(D_{v_A},D_{v_A})|+|\nabla^2w_A(e_2,e_2)|
\le\bigl[Cb\mathsf h_2(\omega+b\nu^2)^2+Cb\nu\bigr]\frac sS .
$$

Therefore $J_{v_A}(e_2)\ge(c_B/2)s/S$ on $P$ for $\nu\le\nu_A$. With
$|\nabla h|\le(1+C\omega)s$ this gives (c).

*Fullness on $\mathcal A$.* Let $e_3(x)$ be the $G$-unit vector in
$\ker\mathrm dv_A$ that is $G$-orthogonal to $e_2$, so
$e_3=\pm\partial_{z_3}+O(\omega+b\nu^2+\nu S)$ and
$|\mathrm dz_3(e_3)|\ge1/2$. For unit $e=\alpha e_2+\beta e_3$
($\alpha^2+\beta^2=1$),

$$
J_{v_A}(e)=\alpha^2J_{v_A}(e_2)+\beta^2J_{v_A}(e_3)+2\alpha\beta\,\nabla^2v_A(e_2,e_3).
$$

On $\mathcal A$ we have $\chi_A=1$ and $H''\ge1$, and the cutoff terms
vanish. Put $M_B=2(C_B+C_\Gamma)+1$ and $m=c_B/2$. Then:

* $\nabla^2w_A(D_{v_A},D_{v_A})=b(s/S)H''(\mathrm dz_3D_{v_A})^2+O(b\nu^2)s/S\ge-Cb\nu^2s/S$;
* $\nabla^2v_A(e_3,e_3)\ge b(s/S)H''/4-M_Bs/S-Cb\nu^2s/S$, so
  $J_{v_A}(e_3)\ge(b/4-2M_B-1)s/S$ for small $\nu$;
* $|\nabla^2v_A(e_2,e_3)|\le|\nabla^2h|+|\nabla^2w_A(e_2,e_3)|\le M_Bs/S$,
  because the leading term contains $\mathrm dz_3(e_2)=0$.

Fix $b=4(2M_B+1+2M_B^2/m+m)$. Then $J_{v_A}(e_3)\ge(2M_B^2/m+m)s/S$, and

$$
J_{v_A}(e)\ge\Bigl[\alpha^2m+\beta^2\Bigl(\tfrac{2M_B^2}m+m\Bigr)-2|\alpha\beta|M_B\Bigr]\frac sS
\ge\tfrac m2(\alpha^2+\beta^2)\frac sS=\frac{c_B}4\,\frac sS ,
$$

using $2|\alpha\beta|M_B\le\alpha^2m/2+2\beta^2M_B^2/m$. Since
$|\nabla v_A|\le2s$, this is $\ge(c_B/8)|\nabla v_A|/S$. Moreover
$|D^2v_A|\le(C_B(1+C\omega)+b\mathsf h_2+1)s/S\le C_A|\nabla v_A|/S$ with
$C_A=2(C_B+b\mathsf h_2+2)$. So (d) holds. The constant $b$ depends only on
$(C_B,c_B,\Lambda)$; $C_A$ depends also on $\kappa$ through $\mathsf h_2$.

*Volume (f).* The inner cube has volume $(1-\kappa)|P|$. In the frozen
coordinates it is a parallelepiped of diameter $\asymp\nu S$, crossed by
$\asymp\nu^{-1}$ periods $\ell_A$ of $z_3$. Its $z_3$-slice area is
unimodal (Brunn–Minkowski: its square root is concave), so its total
variation is at most twice its maximum. Fubini then gives
$|\{x\in\text{inner}:z_3/\ell_A\in\mathbf E\}|\ge((1-\kappa)^2-C\nu)|P|$.
A grid cube of side $\nu^3S$ has $z_3$-extent $\le C\nu^3S=C\nu\ell_A$.
Discarding grid cubes that meet $\partial\mathbf E$ (two endpoints per
period) or the inner-cube boundary loses $O(\nu)|P|$ more. Since
$(1-\kappa)^2\ge1-2\kappa$, (f) follows. $\square$

---

## 7. One generation

**Order of choices.**

1. Fix the pattern of Section 4. This fixes $\zeta_B$, $\lambda_0$,
   $c_\flat$, $C_\flat$, $C^\flat_j$, $\alpha_B$, $\beta_B$ (given $\Lambda$).
2. Set $(C_B,c_B)=(C_\flat+1,c_\flat)$, the weak constants carried by
   every generation.
3. Set $\kappa=\zeta_B/(8(1+\zeta_B))$.
4. Lemma 6.1 with $(C_B,c_B,\kappa)$ gives $b$, $(C_A,c_A)$, $\nu_A$.
5. Lemma 5.1 gives $\mu_0(C_A,c_A,\Lambda)$ and $\mu_0(C_0,c_0',\Lambda)$
   for the seed constants.
6. Choose one reciprocal integer $\nu$ with
   $\nu\le\min\{\nu_A,\lambda_0\}$,
   $\nu^3\le\min\{\mu_0(C_A,c_A),\mu_0(C_0,c_0')\}$, and small enough for
   the finitely many absorptions below. Put $r=\nu^6$, $\mu=\nu^3$,
   $\lambda=\nu$.

**Lemma 7.1 (generation step).** Let $P\subset\Omega$ be a closed cube of
side $\nu S$ with $0<S\le\nu$, on which $h$ is weakly prepared at scale
$S$ with constants $(C_B,c_B)$. Put $s=|\nabla h(x_P)|$ and $\ell=rS$.
There is $v=h+w$, with $w$ smooth and supported in
$\operatorname{int}P$, such that:

1. $\alpha|\nabla h|\le|\nabla v|\le\beta|\nabla h|$ with
   $\alpha=\alpha_B/2$, $\beta=2\beta_B$, and
   $\max_eJ_v(e)\ge c_\sharp|\nabla h|/S$ on $P$, where
   $c_\sharp=\min\{c_B/4,c_A/32\}$;
2. some closed cubes of side $\nu\ell$ in the exact partition of $P$ are
   weakly prepared for $v$ at scale $\ell$ with constants $(C_B,c_B)$.
   Their union $\mathcal R_P$ satisfies
   $M(\mathcal R_P,v)\ge(1+\zeta)M(P,h)$ with $\zeta=\zeta_B/2$;
3. $\|D^jw\|_{L^\infty}\le C_jsS^{1-j}\nu^{-6j}$ for every $j\ge0$.

*Proof.* Apply Lemma 6.1 to get $v_A$. The cubes of $\mathcal A^\sharp$
have side $\nu^3S=\mu S$, and $v_A$ is fully prepared on each at scale $S$
with constants $(C_A,c_A)$. Apply Lemma 5.1 on each of them with
$(\mu,\lambda)=(\nu^3,\nu)$, so $\ell=\mu^2S=\nu^6S=rS$ and the children
have side $\lambda\ell=\nu\ell$. The perturbations have disjoint
supports in the interiors of these cubes. Let $v$ be the sum.

(1) The gradient comparison is the product of Lemma 6.1(a) and Lemma
5.1(1). On a cube of $\mathcal A^\sharp$, Lemma 5.1(1) gives
$J_v\ge(c_A/16)|\nabla v_A|/S\ge(c_A/32)|\nabla h|/S$. Off the interiors
of those cubes $v=v_A$, and Lemma 6.1(c) applies.

(2) Children lie in $\mathcal R_Q$ for some $Q\subset\mathcal A^\sharp$.
By Lemma 5.1(2) they satisfy the Hessian and favorable-direction parts of
(W) with $(C_\flat,c_\flat)$. For the third derivatives, Lemma 6.1(e) and
$\ell=\nu^6S$ give
$|D^3v_A|\le(4C_B\nu^{12}+C^A_3b\nu^{10})s/\ell^2\le|\nabla v|/\ell^2$
for $\nu$ small, using $|\nabla v|\ge\alpha s/2$. So
$|D^3v|\le(C_\flat+1)|\nabla v|/\ell^2$. For the mass, (6.1) gives
$|\nabla h|=s(1+O(\omega))$ on $P$, and Lemma 6.1(a),(f) give

$$
M(\mathcal A^\sharp,v_A)\ge(1-\nu)(1-C\omega)(1-2\kappa-C_\kappa\nu)s|P|
\ge(1-2\kappa-C'\nu)M(P,h).
$$

Summing Lemma 5.1(2) over the cubes,
$M(\mathcal R_P,v)\ge(1+\zeta_B)(1-2\kappa-C'\nu)M(P,h)$. With the chosen
$\kappa$, $(1+\zeta_B)(1-2\kappa)=1+3\zeta_B/4$, which is $\ge1+\zeta_B/2$
after the last absorption of $C'\nu$.

(3) By Lemma 6.1(b),
$|D^jw_A|\le C_jbs\nu^{4-2j}S^{1-j}\le C_jsS^{1-j}\nu^{-6j}$. By Lemma
5.1(3), with center slopes $\le2s$,
$|D^jw_B|\le2C^\flat_js(\nu^6S)^{1-j}\le C_jsS^{1-j}\nu^{-6j}$. $\square$

**Lemma 7.2 (first generation).** Let $P_0\subset U_0$ be a closed cube of
side $\nu$ (scale $S=1$). Applying Lemma 5.1 to each cube of side
$\nu^3$ in its exact partition (full by Lemma 3.1) gives $v=h_0+w$, with
$w$ smooth and supported in $\operatorname{int}P_0$, such that:

* the gradient comparison $(\alpha_B,\beta_B)$ holds;
* $\max J_v\ge(c_0'/16)|\nabla h_0|$ on $P_0$;
* children of side $\nu r$ are weakly prepared at scale $r$ with
  $(C_B,c_B)$ and carry mass $\ge(1+\zeta_B)M(P_0,h_0)$;
* $|D^jw|\le C_jr^{1-j}$.

The third-derivative bound holds because
$|D^3h_0|\le C_0s_{\max}\le\nu^{12}C_0s_{\max}/r^2$. $\square$

---

## 8. Envelopes on $S^3$ with a fixed power gain

**Proposition 8.1.** After fixing the data of Lemma 3.1 and Sections 4–7
(possibly shrinking $\mathcal G$ so that its metrics lie in
$\mathcal G_\Lambda$ on $\overline\Omega$), there are $\gamma>0$ and
$c>0$ with the following property. For every smooth $G\in\mathcal G$ and
all large $k$, there is a smooth real $h=h_k$ on $B=S^3$ with
$h=-a_*t+c_k$ on $\{t\le1/2\}$, where the $c_k$ are any prescribed
bounded constants, and

$$
\|h\|_{C^j}\le C_jk^{\delta(j+1)},\qquad
\max_{|e|_G=1,\ \mathrm dh(e)=0}J_h(e)\ge ck^{-\delta}\ \text{on }\{t\ge1/4\},\qquad
\int_V\sqrt{1+|\nabla_Gh|^2}\,\mathrm dx\ge ck^\gamma,
$$

with $\delta=10^{-6}$. All corrugations lie in one fixed cube
$P_0\Subset V$. The constants $\gamma,\theta$ and all construction
parameters depend only on the seed, Section 4, and $\Lambda$, not on
derivative orders or later accuracy requirements. $C_j$ may depend on
$j$, on the metric, and on the bound for $|c_k|$.

*Proof.* Let $\mathcal P_0=\{P_0\}$. Generation 1 is Lemma 7.2.
Generation $i\ge2$ applies Lemma 7.1 to every cube of $\mathcal P_{i-1}$,
which has side $\nu r^{i-1}$ and is weakly prepared at scale
$S_i=r^{i-1}\le r\le\nu$ with $(C_B,c_B)$. The children form
$\mathcal P_i$. Supports are disjoint within a generation and compactly
inside the parents, so every $h_i$ is smooth and nothing changes outside
$P_0$.

*Mass.* $I_i=\sum_{P\in\mathcal P_i}M(P,h_i)\ge(1+\zeta)I_{i-1}$, so
$\int_V\sqrt{1+|\nabla h_i|^2}\ge I_i\ge I_0(1+\zeta)^i$, and $I_0>0$
is fixed.

*Derivatives.* A point changes at most once per generation, so slopes
are $\le C\beta^i$ and, on $P_0$, $\ge s_{\min}\alpha^i$. By Lemma 7.1(3)
and disjointness,
$\|D^j(h_i-h_{i-1})\|_\infty\le C_j\beta^{i-1}r^{(i-1)(1-j)}\nu^{-6j}
=C_j\beta^{i-1}r^{i-1}r^{-ij}\le C_j\beta^ir^{-ij}$ (also for $i=1$, by
Lemma 7.2). Summing,

$$
\|h_m\|_{C^j}\le C_j\Bigl(1+\sum_{i\le m}\beta^{i}r^{-ij}\Bigr)
\le C'_j\exp\bigl([\log\beta+j|\log r|+1]m\bigr)\le C'_je^{C_*(j+1)m},
$$

with one $C_*$ for all $j$ ($C_*=\log\beta+6|\log\nu|+1$ suffices).
Passing to the fixed atlas adds only fixed chain-rule constants.

*Margin.* Outside $P_0$, Lemma 3.1(2) applies. At a point of $P_0$, take
the last generation $i\le m$ that changes the function there. Its
retained margin is $\ge c_\sharp s_{\min}\alpha^{i-1}/S_i\ge c_\sharp s_{\min}\alpha^m$.
Later perturbations vanish near the point, or all their jets vanish at
their support boundaries. If no generation changes the point, Lemma
3.1(2) applies. So $\max J_{h_m}\ge ce^{-C_*m}$ on $\{t\ge1/4\}$ after
enlarging $C_*$.

*Exponent.* Fix $\theta>0$ with $C_*\theta\le\delta$, and let
$m=\lfloor\theta\log k\rfloor$, $\gamma=\theta\log(1+\zeta)$,
$h=h_m+c_k$. Then $e^{C_*(j+1)m}\le k^{\delta(j+1)}$, $e^{-C_*m}\ge k^{-\delta}$,
and $(1+\zeta)^m\ge(1+\zeta)^{-1}k^\gamma$. These are the three
estimates. Smooth coordinate changes preserve the growth exponents
([P, envelopes.tex lines 647–658]). $\square$

**Remark 8.2 (why fullification is needed; motivation only, not used).**
Consider a single-hump radial well in two transverse variables, a
profile $G(v)$ increasing on $[0,v_0]$ and decreasing to $0$ on
$[v_0,1]$, in the steep-slope limit. In the decreasing part,
strictness requires $-G'<(1+G^2)/(vG)$. This forces
$1+G(v_0)^2<v_0^{-2}$. A region that is full for the next step must avoid
the decreasing part, so its gain is at most
$v_0^2(\sqrt{1+G_0^2}-1)<v_0(1-v_0)$. This is less than the discarded
mass $1-v_0^2$. So radial wells alone cannot produce full repeat regions
with gain. Lemma 6.1 restores fullness without spending mass.

---

## 9. Transfer of the rest of [P] to the base $S^3$

Every item below is a new deduction. It was obtained by reading the
named source lines with $B=S^3$ substituted. Where a source number is a
count that drops in lower dimension, the old number remains a valid upper
bound and is kept.

| [P] location | Base-$S^3$ change | Why the conclusion is unchanged |
|---|---|---|
| framework.tex lines 5–13 | $B=S^3\subset\mathbb R^4$, $y\in\mathbb R^2$ | definitions are dimension-free |
| framework.tex lines 67–83 | $k^2=N(N+2)$; $u_*=\mathrm{Re}(x_1+ix_2)^N$ harmonic on $\mathbb R^4$; $\Delta_{\mathbb R^4}=\partial_r^2+\frac3r\partial_r+r^{-2}\Delta_{g_0}$ | gives $-\Delta_{g_0}u_*=k^2u_*$ and $u_*=(1-t)^{N/2}\cos N\vartheta$ |
| framework.tex, def:certificate | two-dimensional disks; size $\sum\mathcal H^2_{\rm Euc}(D_i^+)$ | same persistence and projection properties |
| framework.tex, prop:step | same statement with $B=S^3$, $k^2=N(N+2)$ | proved by the rows below and Proposition 8.1 |
| envelopes.tex (all) | replaced by Sections 3–8 | same conclusions as `prop:envelope` |
| waves.tex lem:phase-hessian | $e_1,v$ orthonormal in $\mathbb R^3$ | proof is a block computation in $\mathbb R v\oplus v^\perp$; valid in any dimension $\ge2$ |
| waves.tex lem:polynomial-inverse | polynomials on $\mathbb R^3$ (three index choices) | same nilpotent-series proof |
| waves.tex prop:packets lines 242–280 | basis $e_1,e_2,e_3$; $v_2=e_2$, $v_3=(e_2+\eta_ke_3)/\sqrt{1+\eta_k^2}$; **three** pairs $(p,v_2),(p,v_3),(p+Qk^{-3/4}e_1,v_2)$ | $v_2,v_3$ span $e_1^\perp$ with singular value $\ge c\eta_k$; the Hessian-test estimate is per pair |
| waves.tex lines 177–190, 495–514 | jets in $\mathbb C^4$, real $4\times6$ matrices | real parts span the value–$e_1$ plane ($\ge ck^{-3/4}$), imaginary parts span $e_1^\perp$ ($\ge ck^{-9\delta}$): $\sigma_{\min}\ge ck^{-3/4}$ |
| waves.tex lines 282–494, 531–708 | normal coordinates in $\mathbb R^3$ | finite Taylor eikonal/transport solutions, localization and scaled-packet estimates use the envelope bounds and fixed-order chain rules only; exponents unchanged |
| global.tex lines 21–46 | $b_N=\frac N{2k}\log(1-t)$, $N/k\le1$, $N/k\to1$ | $\frac{\mathrm d}{\mathrm dt}(h-b_N)\ge-a_*+\frac N{2k}\ge c_0$ for $a_*<1/4$, large $N$ |
| global.tex lines 76–117 | net of mesh $k^{-10}$ has $\le Ck^{30}\le Ck^{40}$ centers | all bounds stated with $k^{40}$, $k^{2q+41}$ remain true |
| global.tex lem:noncancellation | jet $(u,\partial_1u,\partial_2u,\partial_3u)/W\in\mathbb R^4$; density $\le Ck^{208}$; small-ball $\le Ck^{208-4D}$; grid $\le Ck^{3D+144}$ | union bound $Ck^{352-D}\to0$ at $D=500$; conclusion with exponent $500$ unchanged |
| global.tex lem:signs | $R_x=(kQ_x)^{-1}$; $\int_VkQ\le C\sum kQ_xR_x^3=C\sum R_x^2$; $e_x\in\mathbb R^3$; $H^5(B(0,2))\subset C^2(\overline{B(0,1)})$ in $\mathbb R^3$ since $5>2+3/2$; disks of area $\omega_2\sigma_*^2R_x^2$ | certificate $\ge c_*k^{1+\gamma}$ |
| global.tex lem:correction | none | explicit formula; exponents come from $k^{2q+41}$ and the jet bound |
| global.tex lem:simplicity | harmonic polynomial on $\mathbb R^4$; tangential projection onto $S^3$ | $|\mathrm du|^2=N^2((1-t)^{N-1}-u^2)$; $t$-derivative forces $b''=0$ for $N>1$; Aronszajn unchanged |
| global.tex prop:step proof | none | collar thresholds are dimension-free |
| global.tex lem:persistence | Rellich and $H^3\subset C^0$ in dimension three ($3>3/2$) | same compactness argument |
| global.tex Theorem proof lines 727–885 | $M=S^3\times S^1$, dimension four; $\mathcal H^3_g(Z(u_i)\cap(C\times I_0))\ge K^{-3}|I_0|\mathcal H^2(D)$ | warped-circle identity is dimension-free; nodal bound $\ge c\,i\,k_i^{1+\gamma/2}$ |

The neighborhood $\mathcal U$ of [P, prop:step] is still a $C^1$
neighborhood, since Proposition 8.1 uses only $C^1$ metric bounds.

---

## 10. Proof of Theorem T4

Run [P, global.tex lines 727–885] with base $B=S^3$, using
Proposition 8.1 in place of `prop:envelope` and the rows of Section 9.
This gives positive pairs $\mathcal P_j$ that converge in every $C^r$ to
a smooth positive pair $\mathcal P_\infty$, and eigenfunctions $v_i$ of
$-L_\infty$ with:

* eigenvalues $\lambda_i\in(k_i^2/2,2k_i^2)$, $k_i\to\infty$;
* sign certificates with $|\mathcal C_i|>i\,k_i^{1+\gamma/2}$.

The diagonal budgets, the persistence radii chosen after each stage, and
the choice $c_ik_i^{\gamma/2}>i$ are copied verbatim. Set
$G_\infty^{-1}=A_\infty/\rho_\infty$ and
$q=\rho_\infty\mathrm d\mu/\mathrm d\mathrm{vol}_{G_\infty}>0$. Then
$g=G_\infty+q^2\mathrm d\varphi^2$ on $S^3\times S^1$ satisfies
$\Delta_gf=L_\infty f$ for $f$ pulled back from $S^3$ ([P, eq:circle-operator];
the coordinate divergence identity is dimension-free). So
$u_i=v_i\circ\mathrm{pr}$ are eigenfunctions with eigenvalues $\lambda_i$.

Every longitudinal segment of a certificate cylinder contains a zero. So
$Z(u_i)\cap(C_i^{(a)}\times I_0)$ projects onto $D_i^{(a)}\times I_0$
under a map of Lipschitz constant $\le K$. Hence
$\mathcal H^3_g(Z(u_i))\ge K^{-3}|I_0|\,\omega_2\sum_a(\text{radius})^2\ge c|\mathcal C_i|>c\,i\,k_i^{1+\gamma/2}$.
With $\epsilon_0=\gamma/4$, $\lambda_i^{1/2+\epsilon_0}\le2k_i^{1+\gamma/2}$.
So the ratio is $\ge ci/2\to\infty$. Both $g$ and $\epsilon_0$ are fixed.
$\square$

---

## 11. Validation, checkable risk points, and limits

**What a reviewer should check first.**

1. Lemma 6.1, especially the transport of the favorable direction across
   $P$. It needs the third-derivative bound in (W) and $S\le\nu$ (which
   holds from generation 2 on, since $S_i\le r$). The first generation
   avoids Lemma 6.1 because the seed region is already full.
2. The retained-margin dichotomy in Lemma 5.1 with
   $\mathcal F\subset\ker\mathrm dv=R\ker\mathrm dh$.
3. The order of constants in Section 7. The child weak constants
   $(C_B,c_B)$ come from the pattern alone. $b$ depends on $(C_B,c_B)$,
   $C_A$ also on $\kappa$, and $\nu$ is chosen last. There is no circular
   dependence.
4. The mass accounting: $(1+\zeta_B)(1-2\kappa)>1$ with $\kappa$ chosen
   after $\zeta_B$.
5. The Section 9 rows for waves.tex lines 282–494 and 531–708. I read
   them and found only fixed-order chain-rule and count dependencies on
   dimension. They were not rewritten line by line here. This is the
   largest unrewritten part of the argument.

**Checks performed.** These are reading and derivation checks only: a
line-by-line reading of [P] envelopes.tex (all 659 lines), waves.tex
(all), global.tex (lines 1–403, 403–480, 478–906), framework.tex (all),
and [Q] introduction.tex and s3-profiles.tex lines 1–330. No numerical
experiment was run; none would establish the claim. There is no formal
verification.

**Limits.**

* $\epsilon_0=\gamma/4$ is tiny and is not optimized.
* Dimension three with a power loss is **not** claimed. That would need
  [Q]'s three-dimensional exactification with power control, which is
  outside the frozen scope.
* Dimension four is realized on $S^3\times S^1$ only.
* The metric is not shown to be close to a product of round metrics. It
  lies in a $C^1$ neighborhood of the warped round data, as in [P].
* Novelty is relative to the pinned sources and the dated primary screen
  in `literature-screen.md`. No worldwide priority is claimed.
