from pathlib import Path
BASE=Path(__file__).resolve().parent
SRC=BASE.parent/'kinetic-window-factory/candidate.md'
s=SRC.read_text()
a=s.index('Author role:'); b=s.index('\nH denotes',a)
s=s[:a]+'''Role: repair consolidation; no subagents.

**Status: REVISED CANDIDATE FOR FRESH FULL PROOF REVIEW, NOT ACCEPTED.**
The frozen Factory candidate received REPAIR in `../kinetic-proof-r1/review.md`.
This revision implements its chronology repair and the other findings, with
full arguments below. It is not an independent proof verdict, novelty verdict,
acceptance, campaign increment, manuscript, or public submission. The original
whole-space, full-time, unsmoothed, exactly centered target is preserved.
`response-to-review.md` and `candidate.diff` bind the changes to exact original
and revised bytes. All source truth is stipulated; the new deductions and
extensions of source interfaces remain subject to the fresh proof gate.
''' + s[b:]
s=s.replace('The sequence is moreover C-tight, so the\nconvergence also holds for the uniform topology.','The sequence is moreover C-tight. No weak-convergence assertion is made\nfor the uniform-topology Borel space on all of $D$. On a $J_1$ Skorokhod\nrepresentation of a convergent subsequence with continuous limit, convergence\nis uniformly almost sure; this is only a consequence on that representation.')
a=s.index('\n---\n\n## 2. Lemma W')
s=s[:a]+r'''
### 1.1 One dynamics and a fixed Gaussian budget

Choose $\Gamma$ first as in H. Before fixing an observation list, a moment
order, the complexity cutoff $K$, or a requested error power, choose a common
birth exponent $b_0>0$ from H `eq:sharp-input-bounds`, independently of $L$.
For example $b_0=\beta/4$ is below every $\beta_i\ge9\beta/20$; for small
$\varepsilon$ the bound for $g_i$ follows from `prop:one-root`, the uniform
kinetic Bol bound, and its error at most one. Reserve the fractions of this
Gaussian now. The spatial integration below gives $C^m e^{-b_0E_0}$.
Absorb every fixed-degree link polynomial using at most $e^{b_0E_0/4}$,
leaving $e^{-3b_0E_0/4}$. Of that remaining suppression, reserve a fixed
positive part for the velocity-volume integral and a fixed positive part for
the energy-bin sum, for example use
$e^{-3b_0E_0/4}\le e^{-b_0E_0/4}e^{-b_0P/4}$ on $E_0\in[P/2,P]$.
All per-birth and per-ordinary-atom constants obtained with these exponents
are independent of $K$ and the order. Fixed-degree polynomial absorption
changes only a front constant depending on its degree.

Choose $L$ once large enough for H's coarse and cutoff estimates, its
one-root envelopes, and the sharp summation at this fixed smaller exponent,
so $C T/\sqrt L<1$ and the coarse atom series also converges. This choice
is independent of the later fixed order, accuracy, and $K$. H05
`prop:cutoff` permits every fixed $L\ge L_0$; changing this single auxiliary
parameter does not shorten the supplied interval. All estimates below concern
this one pasted dynamics. Only expansion cutoffs $K,D$ depend on the order
and accuracy.

### 1.2 The inherited continuous target

For completeness, the paid I340 continuity deduction is as follows. H02's
backward propagator, source bound, and field bound give for compact smooth
$\phi$ the mean-square identity
$$
 \zeta_t(\phi)=\zeta_0(\phi)+\int_0^t\zeta_r(A_r\phi)\,dr+W_t(\phi).
$$
For $0<a<b<\beta$, $r\mapsto A_r\phi$ is continuous in $E_a^0$ with bounded
norm. The source field is a strongly measurable $L^2(\Omega)$ map there;
$\mathbb E\int_0^T|\zeta_r(A_r\phi)|^2dr<\infty$. Its indefinite integral has
continuous paths, by Cauchy--Schwarz. The Gaussian noise satisfies
$\mathbb E|W_t(\phi)-W_s(\phi)|^4\le C|t-s|^2$, from the source covariance
and Gaussian fourth moments. Kolmogorov gives a continuous modification.
The displayed identity defines the continuous modification of $\zeta(\phi)$.
A finite intersection of probability-one events handles a finite test list,
with all source joint covariances unchanged. This is the credited I340 §2
argument, not a path-space assertion attributed to H.
''' + s[a:]
a=s.index('### 2.2 The chart and an extended integrand'); b=s.index('\n---\n\n## 3.',a)
s=s[:a]+r'''### 2.2 Physical chart, then a chronological extension

Fix one diagram $G$: its finite lines, C/O flags, slab assignments, a
prescribed **global** chronological order refining all line orders, the
merger/redundant classification, the physical initial-link forest, designated
line $\ell$, and one C-atom $a_*$ incident to it. The order is part of the
ordinary H enumeration, not an additional permutation choice. Summing the
marked-atom indicator over its possible slots gives $N_J(\ell)$.

**Physical coordinates first.** H `lem:sharp-merger-coordinates` gives
$$
 \xi=(v,X,y,(t_g,\omega_g)_g),\qquad
 d\xi=dv\,dX\,dy\,dt\,d\omega,
$$
with $m$ independent birth velocities, one common translation for a connected
component, $p$ relative vectors for the physical initial forest, and time and
normal for each dynamic merger. There are $a=m-1-p$ dynamic mergers. The
physical Jacobian is $\varepsilon^2[(\Delta v_g)\cdot\omega_g]_+$ at a
merger, and a redundant contact has no free parameter or Jacobian. Hence
$$
 \int\mathbf1_{t_{a_*}\in J}\,d|\mathsf D_G|
 \le C_K\mu^{m-h}\varepsilon^{2(m-1-p)}
       \int F_G(\xi)\mathbf1_{t_{a_*}(\xi)\in J}\,d\xi. \tag{W0}
$$
The physical chart retains segment, birth/lifetime, acceptance, slab, and
all chronological tests at this stage. The extension below is a positive
majorant **after** that physical change of variables; it is not a claim of a
new global Jacobian for nonphysical histories.

Let $A_p$ denote the affine origin at time zero of line $p$'s
**pre-first-event segment**, with independent velocity $v_p$ on that segment.
This is an affine-origin coordinate, not generally the value of the eventual
piecewise trajectory at time zero. For endpoints of a physical initial link,
which are born at zero, it agrees on the physical chart with their initial
position. Orient each initial forest edge from $p_l$ to $q_l$ and put
$y_l=A_{q_l}-A_{p_l}$. Initially these differences determine each forest
group up to its own common translation. A line born at a later interface has
its own independent input phase variable; a line **continued** through an
interface has no new input variable. Choose the final representative coordinate
$X=A_{\rm rep}$. This convention fixes the signs of the shear below.

**Prefix construction.** Start every one of the $m$ lines on its pre-first
free segment on the whole real axis. For each current group keep all
previously constructed segments, the current incoming affine segment on each
line, and one unresolved common translation. Process the fixed global slots:

1. At a merger with prescribed $t_g,\omega_g$, solve the relative translation
   of its two previously disjoint groups from H's contact equation
   $X_1-X_2=-d(t_g)-\varepsilon\omega_g$. Translate **every** segment of the
   moved group by that same vector. This leaves all earlier internal
   contacts, their times and velocities, and all initial $y_l$ unchanged.
   Keep one free translation for the newly joined group. Evaluate the current
   incoming segments, extrapolated to $t_g$, and require positive incoming
   flux. If it is not positive, abort the branch. A C-slot reflects the pair
   elastically at this time; an O-slot continues it straight.
2. At a redundant slot the two lines already belong to the same group.
   Use their current relative affine flight and take its unique entering
   intersection with the radius-$\varepsilon$ sphere at or after the later
   of their two preceding incident event times (a missing preceding time
   means $-\infty$). If no transversal entering crossing exists, abort.
   Its time and normal are determined. Apply its C or O update.
3. In **both** cases require the newly computed event time to be strictly
   greater than the preceding **global** slot time; the first global lower
   bound is $-\infty$. Abort otherwise, before proceeding to the next slot.

The existence/incoming tests are denoted $R_G^{\rm ext}$ and the global
order tests $Q_G$. More precisely the weight $R_G^{\rm ext}Q_G$ is the product
of the prefix success tests, extended by zero on the first failure; after
failure no future trajectory needs to be defined. Every test is measurable
from the current prefix and its next prescribed coordinates. Entering times
are measurable roots of the relative-flight quadratic on their transversal
branches. Initial links and merger equations are solved along a forest,
so once the last common translation is fixed by $X$ the construction is
unique. The successful branches are genuine piecewise affine all-time paths
whose segment times increase globally. Simultaneous, grazing, and branch-boundary
null sets have H's original convention.

All $m$ lines may be regarded as present for this extension at **all** real
times. Between events their velocities are constant; each C-update conserves
the pair energy, and each O-update conserves it trivially. Thus their total
energy is exactly
$$
 E_0=\sum_{p=1}^m|v_p|^2
$$
throughout a successful history, not just on its physical lifetimes. Every
subset of slab-$i$ lines has energy at most $E_0$. This is the energy bound
used in the extended flux sum.

The absolute input factor on such a branch remains
$|g_{(p)}(x_p^\xi(b_p),v_p)|$, evaluated at the original fixed birth time
$b_p$. On a nonphysical branch its second argument $v_p$ need **not** equal
the instantaneous velocity at $b_p$. This is allowed for a positive
extension, not asserted to be a new gas law. On the physical chart they agree.
The spatial argument is still $X+d_p$, with identity coefficient in the
common translation, and the Gaussian suppression still uses the independent
coordinate $v_p$.

Define the new extended integrand by
$$
 F_G^{\rm ext,Q}(\xi)=
 \prod_p |g_{(p)}(x_p^\xi(b_p),v_p)|
 \prod_l\mathbf1_{|y_l|\le R\varepsilon}
 \prod_g[(\Delta v_g)\cdot\omega_g]_+
 \mathbf1_{t\in\mathcal D}\,R_G^{\rm ext}(\xi)Q_G(\xi),
$$
where $\mathcal D$ imposes the prescribed slab and relative merger order.
Undefined output factors on aborted branches mean zero. Records have already
been bounded by their suprema; none is reinterpreted on this extension.

**Claim 1 (physical domination).** On the physical chart,
$F_G\le F_G^{\rm ext,Q}$ and $t_{a_*}=t^{\rm ext}_{a_*}$.
All physical global orders and incoming tests succeed. Inductively the
merger equation determines the same group translation; a redundant physical
time lies on the current common segment interval contained in its forward
ray, whose entering root is unique. Therefore the constructed physical
segments and their velocities agree. All omitted physical weights lie in
$[0,1]$. In particular $Q_G=1$ on this domain, so retaining it removes no
physical contribution. ∎

**Why Q is retained.** The original extension fails on the review's strict
four-line chart: mergers at $1/5,2/5$, a redundant contact determined at
$7/15$, then a prescribed merger at $9/20$. The local entering tests all
pass but $7/15>9/20$, so no chronological path has the asserted prefix.
Our third test rejects precisely at the last slot. This counterchart is a
failure of the old enlargement, not a counterexample to the gas or W.

### 2.3 Covariance and the measure-preserving shear

For any real $\theta$ put
$$
 \Phi_\theta(v,X,y,t,\omega)=
 \left(v,\ X-\theta v_{\rm rep},\
       (y_l-\theta(v_{q_l}-v_{p_l}))_l,\
       t+\theta\mathbf1,\ \omega\right).
$$

**Claim 2.** Success or abort is invariant under $\Phi_\theta$, and successful
histories satisfy $x_p^{\Phi_\theta\xi}(s)=x_p^\xi(s-\theta)$ for every line
and every real $s$. All event times, including redundant times, shift by
$\theta$; velocities, incoming fluxes, $R_G^{\rm ext}$ and $Q_G$ are invariant.

To prove this, initially time translation changes the pre-first affine origin
by $A_p\mapsto A_p-\theta v_p$. This gives exactly the displayed $X,y$ shear.
At a merger translate all previously constructed segments of its moved group;
the old contact equation at $t_g$ is exactly the new equation at $t_g+\theta$.
The incoming velocities and its sign test are the same. At a redundant slot
the relative flight and its forward-ray lower bound are translated together,
so the unique entering time and its normal translate as stated. The new
global order test is unchanged because it compares two times both increased
by $\theta$. This proves covariance and matching failure by induction on
prefix length. It uses the affine origin of the **pre-first segment**, not
the generally false identity $x_p(-\theta)=A_p-\theta v_p$ for a full path
that already had earlier events. Future group translations preserve all
prefix comparisons. Uniqueness fixes the final representative. ∎

**Claim 3.** For fixed $v$, the shear is a translation of $(X,y,t)$ and the
identity on $\omega$. On the full parameter space its derivative is block
triangular with identity diagonal. Its inverse is $\Phi_{-\theta}$, so it
preserves $d\xi$. The success set is invariant by Claim 2. This is a
change of variables in the extended parameter integral, using the already
established physical-chart Jacobian only in (W0). ∎

### 2.4 Averaging with the chronology indicator still present

Take $\Theta=\tau$. By Claims 2–3 and Tonelli,
$$
 I:=\int F_G^{\rm ext,Q}(\xi)\mathbf1_{t^{\rm ext}_{a_*}(\xi)\in J}d\xi
 =\frac1\Theta\int_0^\Theta\!\int
 F_G^{\rm ext,Q}(\Phi_\theta\eta)
 \mathbf1_{t^{\rm ext}_{a_*}(\eta)+\theta\in J}d\eta\,d\theta.
$$
First integrate the common translation $X$. Each spatial argument is $X+d_p$
regardless of the fixed birth times and the shift. One spatial $L^1$ bound
and the other spatial suprema give
$$
 \int dX\prod_p|g_{(p)}(X+d_p,v_p)|
 \le\|g_{(p_0)}(\cdot,v_{p_0})\|_1
        \prod_{p\ne p_0}\|g_{(p)}(\cdot,v_p)\|_\infty
 =:B(v)\le C^m e^{-b_0E_0}.
$$
The bound is independent of all displacements, including those depending
on $\theta$. If $u_l=v_{q_l}-v_{p_l}$ then
$$
 \mathbf1_{|y_l-\theta u_l|\le R\varepsilon}
 \le\mathbf1_{y_l\in\operatorname{Cyl}_l},\qquad
 \operatorname{Cyl}_l=[0,\Theta]u_l+B(0,R\varepsilon),
$$
and
$$
 |\operatorname{Cyl}_l|
 \le\pi R^2\varepsilon^2\Theta|u_l|
             +\tfrac43\pi R^3\varepsilon^3.
$$
This is one **simultaneous** shift, not an independent shift per link;
taking the product of containing cylinders is a positive upper bound.
Finally
$$
 \int_0^\Theta\mathbf1_{t+\theta\mathbf1\in\mathcal D}
          \mathbf1_{t^{\rm ext}_{a_*}+\theta\in J}\,d\theta
 \le |J|\mathbf1_{t\in\mathcal D_\Theta},\qquad
 \mathcal D_\Theta=\mathcal D-[0,\Theta]\mathbf1.
$$
All other retained branch factors are shift invariant. Thus
$$
 I\le\frac{|J|}{\Theta}\int dv\,B(v)
       \int dy\prod_l\mathbf1_{y_l\in\operatorname{Cyl}_l}
       \int_{\mathcal D_\Theta}dt\int d\omega\,
       R_G^{\rm ext}Q_G\prod_g[(\Delta v_g)\cdot\omega_g]_+ . \tag{W1-Q}
$$
**The indicator Q has not been dropped.** It is needed for the prefix flux
sum in §2.5. The time-window factor comes from the collective direction,
even if the marked contact itself has no independent time parameter.

For a slab simplex $S=\{s<t_1<\cdots<t_a<s+\tau\}$ with $a\ge1$, fixing its
gaps makes the admissible first-time length $\tau-u_a$; the simultaneous
negative-shift enlargement makes it $\tau-u_a+\Theta$. Hence
$$
 |S-[0,\Theta]\mathbf1|
 =\frac{\tau^a}{a!}+\Theta\frac{\tau^{a-1}}{(a-1)!}
 =\frac{\tau^a}{a!}\left(1+\frac{a\Theta}{\tau}\right).
$$
For $a=0$ its zero-dimensional volume is one. With
$\mathcal D=\prod_iS_i$, its enlargement is contained in
$\prod_i(S_i-[0,\Theta]\mathbf1_i)$. For $\Theta=\tau$ its volume is at most
$$
 \prod_i\frac{\tau^{a_i}}{a_i!}(1+a_i)
 \le(1+n)^L\prod_i\frac{\tau^{a_i}}{a_i!},\qquad n=\sum_i n_i.
$$
The same formula covers an empty merger list. A partial final slab can be
enlarged to the full assigned slab before this bound, with unchanged upper
constant.

### 2.5 Prefix flux tree, link scaling, and summability

We now sum (W1-Q) with the **original** discrete coefficients. Keep $v,y,t$
and the normals fixed and use the discrete tree of successive merger-pair
choices in H `eq:sharp-pair-flux`–`eq:sharp-pair-products`. At a node, all
preceding merger choices and intervening prescribed redundant slots have
already been processed. The incoming velocities for every possible next
pair are the same prefix velocities. A redundant reflection is a function
of that prefix, not of a future pair choice. Prefix failure has weight zero.
All $m$ lines remain present and have conserved energy $E_0$ (§2.2), so for
the eligible slab-$i$ lines on $E_0\le P$,
$$
 \sum_{p<q}[(v_p^{\rm cur}-v_q^{\rm cur})\cdot\omega]_+
 \le\sum_{p<q}|v_p^{\rm cur}-v_q^{\rm cur}|
 \le(n_i-1)\sum_p|v_p^{\rm cur}|\le n_i^{3/2}\sqrt P.
$$
A child subsequently failing existence or Q contributes zero. Induction
therefore bounds the sum of the products **with $R_G^{\rm ext}Q_G$ retained**
by $\prod_i(n_i^{3/2}\sqrt P)^{a_i}$. Initial offsets and spatial translations
do not occur in this bound. Normal integration adds only a fixed constant per
merger. Only **after this prefix bound** replace $R_G^{\rm ext}Q_G\le1$ for
the final positive time-volume estimate of §2.4. No nonchronological branch
has been assigned velocities in the discrete induction.

H's fresh-label weights are unchanged. The deterministic finite forest
exploration and C/O graph fixed them before the physical change of variables.
The shear and a positive indicator enlargement do not label particles again,
choose a new cluster partition, or create a new event-order permutation.
For bounded complexity the denominator is $\prod_i j_i!$ with
$n_i-j_i=O_{K,h,L}(1)$; replacing it by $\prod_i n_i!$ costs a fixed polynomial.
The $O_K(1)$ redundant contacts, initial links and crossing-root choices also
cost only fixed polynomials, exactly as H `lem:sharp-factorials`.

Each link cylinder contributes at most
$C\varepsilon^2(\tau|u_l|+\varepsilon)$. At fixed $T,L$ and
$\varepsilon\le\varepsilon_0$ their product is bounded by
$C_K\varepsilon^{2p}(1+E_0)^{p/2}$ since $p\le K$. In the connected case,
$$
 \mu^{m-h}\varepsilon^{2(m-1-p)}\varepsilon^{2p}=\mu^{1-h}. \tag{W-scale}
$$
The original extra $\varepsilon$ per physical initial link is lost, while the
connected normalization is preserved. With the budget fixed in §1.1,
$(1+E_0)^{p/2}\le C_{K,b_0}e^{b_0E_0/4}$. The remaining Gaussian and dyadic
energy bins give
$$
 \int e^{-b_0E_0/4}dv\le C^m,\qquad
 \sum_{P=1,2,4,\ldots}e^{-b_0P/4}P^{a/2}
       \le C^{a+1}(1+a)^{a/2},
$$
with the lowest bin treated separately as in H. Here $C$ depends on the fixed
Gaussian budget but **not** on $K,p,h$ or the moment order. Thus the numerical
base may differ from that in the unmodified envelope argument; its independence
of $K$ and the order, not a literal equality of numerical constants, is what
is preserved.

The marked slot has at most $n+O_K(1)$ choices. Combining the flux, energy,
time volume, and original factorials leaves, up to its polynomial and
$|J|\mu^{1-h}/\tau$, H's expression
$$
 C^{n+a}\tau^a(1+a)^{a/2}
       \prod_i\frac{n_i^{3a_i/2}}{a_i!n_i!}.
$$
Writing $d_i=n_i-a_i\ge0$, $\sum_i d_i=O_K(1)$, Stirling gives
$$
 \frac{n_i^{3a_i/2}}{a_i!n_i!}
 \le e^{2n_i}(1+n_i)^{d_i}n_i^{-n_i/2}.
$$
Also $\tau^a\le\tau^n\max(1,\tau^{-1})^{O_K(1)}$,
$(1+a)^{a/2}\le C_K(1+n)^{O_K(1)}n^{n/2}$, and
$\prod_i n_i^{n_i}\ge(n/L)^n$. Zero counts have factor one. Therefore the
slab-size bound is
$$
 \frac{|J|}{\tau}\,C_K(1+n)^{d_K+L+1}
              (C\tau\sqrt L)^n\mu^{1-h}. \tag{W2}
$$
There are only polynomially many size vectors at total $n$ for the fixed $L$.
The choice in §1.1 gives $C\tau\sqrt L=CT/\sqrt L<1$ independently of the
polynomial degree. Summing proves Lemma W. This argument includes no-merger
histories and histories with initial links or redundant C-atoms. ∎

The repaired window estimate supplies the collective $|J|$ gain missing from
I340 without introducing a nonexistent time variable at a redundant contact,
without a quantitative cycle-vanishing rate, and without removing the global
chronology test before it has paid for the prefix flux bound.
''' +s[b:]
# Replace short moving-pulse paragraph by explicit arbitrary-accuracy argument.
a=s.index('**Uniformity in $s,t$.**'); b=s.index('\n**Moments.**',a)
s=s[:a]+r'''**Uniformity and arbitrary accuracy.** Fix the cumulant order $j$ and an
error power $P$. Always end the two-pulse construction at the same full time
$T$, with pulses $-\phi$ at $s$ and $+\phi$ at $t$ on at most $j$ designated
labels. Its root-output maps have bounded marks $|y|\le2B$ for all $s,t$.
The finite autonomous/forest identities and all compatibility/acceptance
weights depend on unmarked trajectories. Removing pulse-to-segment selection
restrictions for an absolute bound costs at most a fixed polynomial in graph
size, since there are two pulses and a fixed number of designated lines.
For coarse estimates it costs a cutoff power of fixed degree, already
absorbed in H's fixed-root/record complexity losses. The stopped positive
kernels and the crude TV propagation operator likewise see only a supremum
of the bounded test, not its pulse times. Thus their actual kernel proofs,
not a presumed uniformity of a fixed-list theorem, give one positive
majorant for **all** $(s,t)\in[0,T]^2$.

Concretely choose the unweighted high-complexity accuracy $A>P+2j+2$ and
then one $K$ making H04's bound
$C_{h,2}\varepsilon^{-C_*h-C_2+c_*K/2}\le\varepsilon^A$ for every $h\le j$.
Its constants just described are uniform in $s,t$. After this $K$, choose the
initial-tail target $M>P+2j+2$ and $D>2K+M$. Erasing an initial tail costs at
most $\varepsilon^{-2K}$ and yields the stated
$C\varepsilon^M\mu^{1-h}$. Multiplication by $\mu^h$, $h\le j$, then leaves
$O(\varepsilon^{M-2})$ for these tails and $O(\varepsilon^{A-2j})$ for the
coarse errors. The variation $e^{-c\Lambda_L}$ beats every fixed power,
uniformly in pulse positions. All tests in these errors are bounded powers
of $y$ or $|y|$; no Gaussian weight for an arbitrary microscopic remainder
is invoked. Increasing the targets first pays any finite cross product in
the moment identity. The dynamics and the fixed $L$ do not change.
''' +s[b:]
a=s.index('### 4.1 Lemma E′'); b=s.index('\n### 4.2 Proposition M',a)
s=s[:a]+r'''### 4.1 Lemma E′: a decorated final-partial-slab kernel

Let $(i-1)\tau\le a<b\le i\tau$, and end the hierarchy at $b$. Put
$r_p=\mathbf1\{\text{velocity of designated root }p\text{ jumps in }(a,b]\}$.
This is a bounded measurable function of its autonomous **final-slab**
history, not a function asserted recoverable from the endpoint.

**Lemma E′.** On the output space $(z_p(b),r_p)$, the normalized factorial
hierarchy of the same pasted dynamics has H's retained connected-diagram
cumulant expansion and unweighted TV/coarse/initial-tail decomposition,
with constants uniform in $a,b$ and the final partial endpoint. The retained
flag obeys $r_p\le N_{(a,b]}(p)$ on its actual history. Thus for each fixed
$h$ and arbitrary $P$,
$$
 \left|\mu^h c_{h,b}^{\varepsilon,\mathrm{dec}}
                    (r_1\cdots r_h)\right|
       \le C_h\mu(b-a)+C_{h,P}\varepsilon^P. \tag{E′}
$$
The statement for an order with some flags omitted follows by projection.

**Proof from the finite kernels.** In H04 `eq:retained-kernel`, for each
fixed autonomous cluster partition replace only the final output delta by
$$
 \delta_{\left((z_p^{\Psi_{\mathcal C}}(b),
           r_p(\Psi_{\mathcal C}|_{(a,b]}))\right)_{p\in S}}.
$$
Use the same replacement in the positive stopped kernel. The accepted
collision caps make each autonomous final history finite; evaluation of the
flag is measurable on the common full-measure history space. H04
`eq:autonomous-observation` applies to any bounded measurable test of these
root histories. Apply its finite Janossy and rooted-forest proof with this
new delta kernel. Spectators still cancel **pointwise before integration**;
choosing $j$ fresh reached labels leaves exactly $\mu^j/j!$, by H's binomial
identity. Thus the exact one-slab formula and its positive variation remainder
hold on this decorated output space, not just when testing its endpoint
projection. The dynamics and its acceptance rule have not changed.

Earlier slabs need no flag. Compose their ordinary unmarked kernels with
this final decorated kernel. In the final slab keep each designated-root
history explicit: a flagged singleton is not resummed into an **unmarked**
final $g_i$. Lower independent one-root inputs may retain H's canonical
unmarked resummations. For estimates one may open their finite one-root
definitions along the at most $h$ designated final particle lines down to
zero, keeping a constant dummy record there if needed. This is H's
record-preserving finite regrouping and projection identity; it does not
sample new particles or duplicate an input at an interface. If this
bookkeeping requires bottom continuations for the coarse class, add at most
$h$ dummy straight-root links as in H03 `lem:dhm-dummies`(iii), at fixed loss
$\varepsilon^{-h\upsilon}$, together with the top-root deficit
$\varepsilon^{-C_*h}$. These are positive-estimate devices only. Their fixed
extra complexity and powers are absorbed by the subsequent choice of $K$;
remove them before the low-complexity physical-link estimate W. The flag
itself is still computed only by the final output kernel. This avoids both
losing a final flag in an unmarked singleton resummation and introducing a
record or line for every collision.

Decorated root outputs factor over disjoint global components, since each
$r_p$ depends only on its own component history. Expand lower one-root sums
as finite expressions for this algebra. Assigning fresh labels to components
has exactly the multinomial cancellation in H04 `lem:diagram-labels`.
Consequently the retained decorated hierarchy satisfies
$$
 \widehat F^{\mathrm{dec}}_{b,S}
    =\sum_{\pi\in\mathcal P(S)}\bigotimes_{B\in\pi}
                         D^{\mathrm{dec}}_{b,B},
$$
so finite factorial-cumulant inversion keeps precisely the connected
**decorated** diagrams. This is an identity of measures on the decorated
output, before testing $r_1\cdots r_h$.

Pushforward by the new delta map does not increase total variation. More
explicitly, every positive forest/stopped integrand tested against a bounded
function of the flags is bounded by the identical unmarked positive
integrand times its supremum. Therefore H's crude TV operator and its stopped
variation induction work with this new output. Partial-slab time restrictions
only decrease those upper majorants; there are at most $L$ possible final
slab indices. Any fixed root/continuation losses from the preceding paragraph
are the same sort of fixed losses already allowed in that induction. The
normalized actual decorated factorial mass is
$\mu^{-|S|}\mathbb E(N)_{|S|}\le1$ (and its restriction by flags is smaller),
because $N$ is conserved. The retained decorated measures have variation at
most $1+e^{-c\Lambda_i}$. Taking the difference of the finite partition
polynomials for the actual and retained hierarchies hence gives the same
$C_he^{-c\Lambda_i}$ cumulant error. No density or Gaussian norm is assigned
to an arbitrary TV error.

For fixed accuracy choose $K$ using the positive coarse bound, including
these fixed root losses. Its positive integrand has no dependence on the
values of $a,b$ except through a multiplier at most one and the final time
domain restriction. It is thus uniform in those times. Choose $D$ afterward
as in §3. For the retained low-complexity part, refine each autonomous C-cluster
by its complete ordered accepted C history, exactly as H04
`lem:one-root-bridge` and `lem:stopped-variation`. A designated root can
change velocity only at one of these displayed C-atoms. Thus, on every
physical retained history, $r_p\le N_{(a,b]}(p)$; O-atoms do not change its
velocity. Bound the other flags by one and apply W to one designated root,
then use the original fresh-label factor and normalization. The uniform
unweighted remainder powers can be made arbitrarily large before multiplying
by $\mu^h$. This proves (E′) and the claimed decomposition. ∎

The decorated point process restricted to $r=1$ has factorial measures
$F_{p,b}^{\varepsilon,\mathrm{dec}}(r_1\cdots r_p)$ and factorial cumulants
$c_{p,b}^{\varepsilon,\mathrm{dec}}(r_1\cdots r_p)$: restriction to the flagged
output commutes with the tensor-product partition identity. This is the
hierarchy used for Count below. It is neither an illicit two-record endpoint
test nor an assertion that H's additive-pulse mark already records collisions.
''' +s[b:]
# Add microscopic convention and precise count diagonal formula, preserving proof.
s=s.replace('Since $3\\alpha<\\tau$, split each $I_k$ at an\ninterface', 'For sufficiently small $\\varepsilon$, $3\\alpha<\\tau$; split each $I_k$ at an\ninterface')
s=s.replace('so\n$\\mathbb E[\\mathrm{Count}^3]\\le C(\\mu\\alpha+\\mu^3\\varepsilon^P)$.','so the bounds for $p=1,2,3$, together with\n$\\mathrm{Count}^3=\\mathrm{Count}^{(3)}+3\\mathrm{Count}^{(2)}+\\mathrm{Count}$, give\n$\\mathbb E[\\mathrm{Count}^3]\\le C(\\mu\\alpha+\\mu^3\\varepsilon^P)$.\nEvery diagonal contribution is included. The arbitrary source accuracy was\nchosen before this finite partition expansion to absorb cross products.')
s=s.replace('Combining the three bounds proves the claim. ∎','''All interval tests are half-open $(a,b]$ and phase paths are right-continuous.
At a slab interface the physical state is pasted without a jump. A collision
at the left endpoint is already included in that endpoint's right-continuous
state; collisions at the right endpoint belong to the test. These conventions
also cover deterministic grid endpoints. Combining the three bounds proves
the claim. ∎''')
a=s.index('2. *Transfer* (I340');b=s.index('\n3. *Identification.*',a)
s=s[:a]+r'''2. *Transfer* (I340 §3, credited and explicit). Let $S_t=\sum_i\phi(z_i(t))$
   and $\widehat S_t=\sum_i\phi(\hat z_i(t))$. On H05's global coupling event
   $E^\varepsilon$ of any discrepancy, for all times simultaneously,
   $\sup_t|S_t-\widehat S_t|\le2\|\phi\|_\infty N\mathbf1_{E^\varepsilon}$,
   with $\mathbb P(E^\varepsilon)\le C\varepsilon^{21/20}$. Hölder and the
   fixed $22$nd moment of $N/\mu$ give
   $$
    \sup_t\frac{|\mathbb ES_t-\mathbb E\widehat S_t|}{\sqrt\mu}
       \le C\varepsilon^{-1+(21/20)(21/22)}
       =C\varepsilon^{1/440}\longrightarrow0.
   $$
   The uncentered paths agree at every time off $E^\varepsilon$; its probability
   tends to zero. Hence $\|X^\varepsilon-\widehat X^\varepsilon\|_\infty\to0$
   in probability, for a fixed finite coordinate vector as well. The identity
   time change bounds $J_1$ distance by this supremum discrepancy. The modulus
   inequality $w(X,\lambda)\le w(\widehat X,\lambda)
   +2\|X-\widehat X\|_\infty$ transfers C-tightness. No fourth-moment
   estimate for the true flow on $E^\varepsilon$ is assumed.''' +s[b:]
s=s.replace('So the whole sequence converges, in $J_1$ and in the uniform topology. ∎','''Thus the unique subsequential law is the continuous Gaussian law, and the
   whole sequence converges in $J_1$ with C-tightness, as stated. This does not
   identify the processes as random elements of the nonseparable uniform-Borel
   space on all of $D$. ∎''')
a=s.index('## 7. Checks a reviewer should make'); b=s.index('\n## 8. Contribution limits',a)
s=s[:a]+r'''## 7. Repair validation and excluded shortcuts

- **Chronology (R1).** The globally ordered prefix construction in §2.2 retains
  $Q_G$; its shift invariance is proved in §2.3 and it remains in (W1-Q)
  through the discrete flux induction in §2.5. Only then is it discarded for
  a positive time-volume bound. The exact $7/15>9/20$ counterchart is rejected.
- **Uniformity (R2).** §3 derives one positive moving-two-pulse majorant and
  specifies the order of arbitrary-accuracy choices before multiplying by
  $\mu^h$. It makes no weighted claim for generic expansion remainders.
- **Decorated kernel (R3).** §4.1 defines E′ once, at the final root-output
  delta; proves component inversion, TV domination, uniform partial endpoints,
  and the jump-to-C-atom inequality; and states fixed bookkeeping losses rather
  than recovering flags from an unmarked endpoint density.
- **Gaussian base and factorials (R4).** The budget and $L$ are fixed in §1.1
  before order and $K$. Only polynomial degrees and front constants depend on
  those later parameters. The original fresh-label denominator is retained in
  §2.5. Link cylinders lose the link's extra $\varepsilon$ but preserve (W-scale).
- **Cumulants and microscopic scale (R5–R6).** §3 uses the exact block factor
  $\mu^{|\pi|}$. §4.2 keeps all falling-factorial diagonals in Count$^3$ and
  gets $\mu^{-1/2}+\mu^3\varepsilon^P$ at $\alpha=\mu^{-3/2}$. §5 uses
  $\theta=1/8$, giving $\mu^{-1}\alpha^{-4\theta}=\mu^{-1/4}$.

A second-moment union bound at the same scale gives only
$(T/\alpha)(\mu\alpha)/(\eta^2\mu)=T/\eta^2$, which does **not** vanish;
the earlier claim $T\mu^{1/2}/\eta^2$ was arithmetically wrong. The actual
proof uses third moments. Small individual jumps alone, an unproved
collision-current martingale, independent slab resampling, and qualitative
cycle smallness under a singular GRR cutoff remain excluded. There is no
new independent time variable at a redundant contact and no separate shift
per initial link.

The accompanying exact checks reproduce the rejected counterchart, test the
prefix indicator under rational shifts and a chronological variant, and
check scaling and exponent arithmetic. They are supporting finite checks,
not proof certificates for W, E′, the expansion, or the stochastic limit.
The old Monte Carlo checks are not rerun or used to justify this repair.
''' +s[b:]
s=s.replace('- Formal support: none yet.', '- Formal support: no full theorem certificate exists.')
s=s.replace('at the pin. Upstream theorem truth is stipulated. Every deduction below is new\nto this file unless credited.', 'at the pin. Upstream theorem truth is stipulated. The collective-shift mechanism\nand the unchanged increment, microscopic, and chaining arguments are the Factory\ncandidate; the global-order repair and the specified interface clarifications\nare credited to the first proof reviewer. I340 supplies the earlier paid partials.\nThis file consolidates and checks those deductions; it does not claim them as\na second discovery.')
s=s.replace('with **exact** microscopic centering at every $t$.', r'''
with **exact** microscopic centering at every $t$.
For each fixed $\varepsilon$, the finite-particle phase paths have the standard
right-continuous velocity convention. Their bounded-test sums are càdlàg;
their expectations are càdlàg by dominated convergence using
$|\sum_i\phi(z_i(t))|\le\|\phi\|_\infty N$ and $\mathbb EN<\infty$.
Thus the centered finite vector is a random element of the usual $J_1$
Skorokhod space, whose Borel sigma-field is generated by coordinate evaluations.
''')
s=s.replace('argument, not a path-space assertion attributed to H.', r'''argument, not a path-space assertion attributed to H.
The Gaussian law is exactly H02 `eq:target-covariance`:
$$
 K_{\phi,\psi}(t,s)=\int f_0\,U(0,t)\phi\,U(0,s)\psi\,dz
   +\int_0^{t\wedge s}C_r(U(r,t)\phi,U(r,s)\psi)\,dr,
$$
where $U$ is its backward propagator and $C$ is H01 `eq:noise-form` with
ordinary sphere area and the factor $1/2$. In particular the initial covariance
is $\int f_0\phi\psi$, with no fixed-particle-number subtraction.
''')

s=s.replace('  **not** been checked. A separate primary-literature contribution review must\n  decide novelty.', '  checked in the separate `../kinetic-contribution-r1/review.md`, which returned\n  SUBSTANTIAL **conditional on validity** for this one bridge, with bounded\n  primary coverage in its `sources.md`. That review concerns the frozen Factory\n  input and does not validate this revised proof or certify worldwide priority.')
a=s.index('- The new ingredient is Lemma W.')
b=s.index('- Formal support:',a)
s=s[:a]+'''- The proposed bridge is Lemma W. The separate
  `../kinetic-contribution-r1/review.md` returned SUBSTANTIAL **conditional on
  validity** for this one package, with bounded primary coverage in its
  `sources.md`. That review concerns the frozen Factory input. It does not
  validate this revised proof or certify worldwide priority. The BGSS/DHM
  primary papers were not freshly reopened by this repair agent.
'''+s[b:]
s=s.replace('Pushforward by the new delta map does not increase total variation. More\nexplicitly, every positive forest/stopped integrand tested against a bounded', 'At the level of each positive history kernel, the new delta pushforward\npreserves its mass. This does not lift an endpoint TV estimate to histories:\nwe rerun the positive history estimates before the new output pushforward.\nIn particular every positive forest/stopped integrand tested against a bounded')
(BASE/'candidate.md').write_text(s)
