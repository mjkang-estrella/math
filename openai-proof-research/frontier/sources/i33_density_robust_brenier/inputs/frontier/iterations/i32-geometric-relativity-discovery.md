# I32 — geometric/relativity discovery: developed endpoint gap

**Disposition:** no substantial finding nominated. This is a standalone developed-gap record, with a technical $L^p$ deduction, two constructive attacks on a stronger logarithmic endpoint, and explicit smooth geometric obstruction tests. The endpoint statement below is **not proved**. The $L^p$ deduction is an author deduction from stipulated proof operations, not an independent proof-review verdict. It is not offered as a substantial discovery merely because its statement is stronger than the printed headline.

Work is restricted to this report and the two assigned I32 artifact directories. No agents, index changes, staging, commits, or publication were used. The complete brief and relevant prior inputs are frozen under `frontier/sources/i32_geometric_relativity_discovery/inputs/`. All openai/math proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises, including their internal constructions; their truth is not audited here.

## 1. Discovery decision and the three screens

The complete 749-manuscript inventory and 9340-file corpus were used read-only. Every corpus byte hash and Git blob was checked against the existing manifest and complete preprint tree; zero mismatches were found. This is an integrity/inventory check, not a claim to have read 9340 texts semantically. The title/README screen, exact source passages subsequently opened, pinned raw URLs, and dependency contracts are recorded in the accompanying source manifests. The truncated root-tree cache was not used.

The three screens concern different operations: variational equality on original gravitational data; nonlinear propagation plus chart-independent holonomy in a Lorentzian evolution; and transport of cell masses/moments in a convex variational problem. They are not three values of a parameter in one theorem.

| Screen | Concrete residual target | What would be substantial | Decision |
|---|---|---|---|
| Charged Penrose, family260 | For connected time-symmetric charged horizons with area $4\pi$, $0\le Q\le1-\eta$, divergence-free fields, $R\ge2(\vert E\vert ^2+\vert B\vert ^2)$, and $m-(1+Q^2)/2\to0$, obtain an original-metric degeneration/stability theorem allowing removal of genuinely negligible regions and replacement of the boundary by almost-area-preserving enclosures, without bounded-geometry assumptions. | A charged counterpart of a mass-capacity/spike-removal mechanism that controls the original metric. Equality alone and spherical ODE estimates do not do this. | Not selected: exact slicing freedom already kills stronger tensor stability; the source equality multiplier is not quantitative; the needed charged mass-capacity compactness is absent from the inspected interface. |
| Kerr, family264 | At a fixed rotating subextremal center and in the source's exact weighted smooth topology, decide generic future inextendibility for a continuous metric whose weak connection lies in $L\log L_{\mathrm{loc}}$. | A nonlinear tail/propagation and observation mechanism that survives below every $L^{1+\epsilon}$, with arbitrary ambient charts and full-MGHD exits. | Selected for deep development. Existing operations yield the technical all-$p>1$ route below. Two attempts at $L\log L$ fail at explicit, different interfaces. |
| Brenier transport, family374 | For fixed convex compact $K\subset\mathbb R^d$, $d\ge2$, compact target container $Y$, and every probability $f\,dx$ on $K$ with $0<c\le f\le C$, prove $\lVert T_\mu-T_\nu\rVert _{L^2(f)}\le C_{K,Y,c,C}W_2(\mu,\nu)^{1/3}$, uniformly in both targets and with no derivative norm of $f$. | A density-robust cell-moment mechanism uniform through tiny masses, coalescing sites and arbitrary atom counts. | Not selected: exact midpoint domination is the unresolved operation. Ordinary interpolation is already available and is not the bridge. |

Named connections are, respectively, stability of the Penrose inequality, regularity-sensitive strong cosmic censorship, and quantitative stability of Brenier maps. The local MathDB records examined for these names returned no matching record (`mathdb-observed.json` is empty). No MathDB score, ranking, or numerical relevance is asserted. Absence from this local check says nothing about the global database.

For precision, the first screened target fixes $\eta\in(0,1)$ and a charge $Q\in[0,1-\eta]$, and quantifies over every sequence in the stated connected time-symmetric class with horizon area $4\pi$ and deficit tending to zero. Its proposed conclusion is existence of connected closed exterior regions $N_i$ with boundary decomposed as $\Sigma_i^a\cup\Sigma_i^s$, connected major boundary $\Sigma_i^a$ of area tending to $4\pi$, and minor boundary area $|\Sigma_i^s|\to0$, such that for every choice of basepoint on the major boundary the intrinsic length spaces $N_i$, with Riemannian volume, converge in pointed measured GH sense to the exterior of RN of mass $(1+Q^2)/2$, charge $Q$, based on its horizon; the major boundaries with their intrinsic length metrics should converge in measured GH sense as well. This is an unproved target, not a conclusion of the screen. If charges vary, one must first pass to a convergent charge subsequence and specify that limiting model. No convergence of the unmodified original horizons is demanded.

### 1.1 Charged original-data equality: exact scope and why it is not a modulus

Let PC denote *The spacetime Penrose inequality with charge and original-data rigidity*, October 5. Its `statements.tex`, Definitions `def:data`, `def:full-cut`, `def:rigidity-class`, and Theorems `thm:numerical`, `thm:rigidity`, `thm:converse`, give the following contract.

The exterior is smooth, connected, oriented, complete with nonempty compact smooth boundary included, and has exactly one asymptotically Euclidean end. Its metric and second fundamental form satisfy $g-\delta=O_2(r^{-q})$, $K=O_1(r^{-1-q})$, $q>1/2$; fields are $O_1(r^{-2})$; the indicated flux limits are finite. In geometric normalization,

$$
2\mu=R+(\operatorname{tr}K)^2-|K|^2,\quad J=\operatorname{div}(K-\operatorname{tr}K\,g),
\quad\mu_m=\mu-|E|^2-|B|^2,\quad J_m=J-2(E\times B)^\flat.
$$

Require $\mu_m\ge|J_m|$, divergence-free fields, and $\mu,|J|\in L^1$. A **full cut** is the entire boundary of a connected exterior submanifold containing the whole distant end, including every component and any portion coincident with the original boundary. Put $r_A=(\inf_\Gamma |\Gamma|_g/(4\pi))^{1/2}$, $Q=(Q_E^2+Q_B^2)^{1/2}$. The source proves positivity of the infimum; it is not an extra hypothesis.

Componentwise weak future trapping, or separately chosen future/past signs, gives $E_{\rm ADM}>|P|$, $m=(E_{\rm ADM}^2-|P|^2)^{1/2}\ge Q$, and

$$
r_A\le m+\sqrt{m^2-Q^2}.
$$

The polynomial inequality $m\ge(r_A+Q^2/r_A)/2$ is asserted only for $r_A>Q$. Disconnected horizons cannot silently be moved onto that branch. Equality classification additionally requires connected marginal boundary, outermostness against all full weakly trapped enclosures, outer area minimization, and $m>Q$. The **entire original quadruple** is a spacelike slice of dyonic RN, with mass/flux matching and a full future-horizon cross-section or bifurcation sphere. It need not be the static slice. There is no extremal equality classification.

The inspected equality proof operates directly on the original data. At equality it sets

$$
c_h=\frac{1-Q^2/r_h^2}{r_h}>0,\qquad b=(E/m,-P/m),\qquad \mathcal L=b\cdot(E_{\rm new},P_{\rm new}).
$$

Strict compactness of minimizing frontiers gives the one-sided envelope derivative $a'_+(0)=\min_M\frac12\int_{\partial M}\operatorname{tr}_{T_M}h$. Positive-cone separation, using a strict conformal direction with active constraint derivative at least $8r^{-3-\beta}$, yields a probability measure on minimizing frontiers and nonnegative constraint/boundary multipliers:

$$
16\pi\mathcal L'-c_h\int a'_M(h)\,d\pi(M)
=\int\mathfrak C'\,d\Lambda-\int\theta'\,d\zeta.
$$

The normal-variation proof realizes finite Gaussian/Maxwell jets, regularizes matter stress by $J_m\otimes J_m/(\mu_m+\delta)$, proves its $C^1$ convergence, and removes cancellation between frontier tangent planes using their compatibility and strict perimeter compactness. These are reusable operations, not merely the equality headline. They still give no deficit-controlled approximate multiplier: feasibility radii and Taylor remainders depend on the datum; compactness is of the minimizing family for that datum; $c_h\to0$ at extremality. Inserting a desired bound for an approximate adjoint into the hypotheses would not solve this interface.

The October 5 axisymmetric KN companion is stronger in a different direction, not an unrestricted extension of this scope. It assumes an exterior diffeomorphic to $\mathbb R^3\setminus B$, an effective $2\pi$-periodic $U(1)$ action preserving the data, electrovacuum, $P_{\rm ADM}=0$, $g-\delta=O_4(r^{-1})$, $K=O_3(r^{-3})$, controlled Coulomb field tails, a connected outermost outer-area-minimizing marginal boundary, and $A\ge4\pi\sqrt{Q^4+4J^2}$. Its conserved angular momentum includes the electromagnetic primitive correction after duality rotation. It proves

$$
m^2\ge A/(16\pi)+Q^2/2+\pi(Q^4+4J^2)/A.
$$

The cut lemma actually constructs a univalent conformal cut of prescribed capacity with pointwise inner length density from lower bounds for **every** meridional crossing. The construction trims puncture tails, smooths a lower weight, and replaces critical levels by an essential foliation. These geometry-dependent choices do not give uniform cut geometry from small deficit. Original-data rigidity is again a slicing statement in the strict branch, not a stability theorem or an extremal classification.

The nonmaximal AdS companion fixes $\Lambda=-3$, one hyperbolic end, $g-b\in C^{2,\alpha}_\tau$, $K\in C^{1,\alpha}_\tau$, $3/2<\tau<3$, the stated weighted integrability of $\mu+|J|+|K|^2$, DEC, and future-timelike **metric four-flux** mass. It proves $m_{\rm AH}\ge(r_A+r_A^3)/2$, with original SAdS slicing rigidity under the connected horizon hypotheses. The spatial components of this mass vector are not ADM momentum; arbitrary spacetime slices need not preserve the computed mass. I use this companion to delimit the screen, not to claim a proved charged AdS modulus.

The September 27 replacement mechanisms do not supply the missing metric compactness. In the CKS Bondi transfer, at fixed replacement radius (R), $G_R\ge(1-CR^{-3})g$ protects **all** cut areas, the retained compact region is unchanged, $P_R=0$, and $E_R=m_B+c_{R,\infty}$ with $0\le c_{R,\infty}\le2R^{-1/2}$. The tail constants need not be uniform in (R). The four-dimensional weak-decay boundary transfer fixes (R), then strictifies by $s>0$, solves/exhausts and removes its conformal floor at fixed ((R,s)), takes $s\downarrow0$, and only then $R\to\infty$. Its area comparison is one-sided. Neither result authorizes exchanging those limits with a near-equality sequence.

An operation-level primary comparison was made first with Dong v2 and then with the stronger current [Dong, arXiv:2402.10299v4](https://arxiv.org/abs/2402.10299v4), after checking the submission history. Theorem 1.1 allows disconnected outermost minimal boundaries with total areas merely converging to the limiting area. It produces a connected retained exterior with connected major boundary of the correct limiting area and minor boundary area tending to zero, and proves intrinsic pmGH convergence from every major-boundary basepoint and measured GH convergence of that boundary. Doubling/conformal mass-capacity reduction and harmonic-coordinate control are essential. In v4, Lemma 6.1 passes the potential through the excised domains in weak $W^{1,2}$, and Proposition 6.2 explicitly removes the boundary flux using its vanishing area to preserve the limiting equation. The final proof invokes Bray flow to reach connected minimal boundaries and a small mass-capacity gap. Adding charge needs a compatible flux/energy passage and a charged rigidity identification; the inspected PC deformation does not supply those. [Lee–Sormani, 1109.2165v1](https://arxiv.org/abs/1109.2165v1) already places appended cylinders in rotational near-equality geometry. The original-horizon shape cannot simply be required to converge: the collar construction in [Cabrera Pacheco–Cederbaum–Gehring–Peñuela Díaz, item3368155 version 3](https://pure.mpg.de/rest/items/item_3368155_3/component/file_3368156/content), Theorem 5.1 and its proof, prescribes a boundary metric and glues a slowly varying collar to a subextremal model at near-optimal mass under its stated charge/cosmological restrictions. Its trace-free path, long collar parameter, strict mean-convex foliation, and Hawking-mass limit are actual construction operations. I do not erase the displayed restrictions on $\Lambda,\kappa,q$ or claim from that version an unrestricted AF charged result.

#### A smooth exact-equality obstruction, with all enclosure conditions checked

Fix $0\le Q<1$, $m=(1+Q^2)/2$, $F=1-2m/r+Q^2/r^2$, so $r_+=1$. In RN take a radial graph $T=h_n(r)$, where

$$
h_n(r)=\epsilon n^{-1}\chi(r)\sin(nr)
$$

and $\chi$ is smooth, compactly supported in $1+\delta<r<R$, equal to one on a nonempty interval. Choose a fixed sufficiently small $\epsilon>0$ so that $s_n=Fh'_n$ obeys $|s_n|\le1/2$ for every $n\ge1$. The induced metric is

$$
g_n=F^{-1}(1-s_n^2)\,dr^2+r^2\sigma.
$$

It is uniformly comparable to the static metric and is exactly static near the horizon and infinity. It is smooth at the bifurcation boundary in proper radial coordinates and complete with boundary. Pull back the smooth RN Maxwell field; the constraints are electrovacuum, fields are divergence-free, charges are fixed, and ADM momentum is zero with mass $m$.

The closed two-form $\omega=dA_\sigma$ has comass $r^{-2}\le1$ for $g_n$. Its flux over every oriented full cut is $4\pi$, by Stokes on the compact region between that cut and a distant coordinate sphere (including all components). Hence every cut has area at least $4\pi$, achieved at $r=1$.

The future normal and outward radial unit tangent have radial components

$$
n^r=\frac{\sqrt F\,s_n}{\sqrt{1-s_n^2}},\qquad
\nu^r=\frac{\sqrt F}{\sqrt{1-s_n^2}}.
$$

Thus each coordinate sphere with $r>1$ has

$$
\theta_+=\frac{2\sqrt F}{r}\frac{1+s_n}{\sqrt{1-s_n^2}}>0.
$$

This formula depends on $h'_n$, not $h''_n$. A hypothetical smooth compact full weakly trapped enclosure has a maximum of $r$; there its end-pointing normal is radial outward, its tangent plane is that of the coordinate sphere, its mean curvature is at least that sphere's, and its tangential $K$-trace is identical. Its expansion would be positive there. This proves outermostness even for disconnected candidate enclosures. The original boundary has zero expansion because the graph is static near it. All PC connected-horizon assumptions hold, and the deficit is exactly zero.

Inside $\chi=1$, choose critical points $r_n$ with $nr_n=\pi/2+2\pi k_n$ staying in a fixed compact subinterval. Then $h'_n(r_n)=0$, $h''_n(r_n)=-\epsilon n$. Direct graph differentiation with the source's future-normal sign convention gives

$$
K_{rr}(r_n)=\sqrt{F(r_n)}h''_n(r_n),\qquad
|K|_{g_n}(r_n)\ge F(r_n)^{3/2}\epsilon n\longrightarrow\infty.
$$

This is an invariant obstruction to any deficit modulus forcing the original $K$ toward zero, including after spatial diffeomorphisms. It is **not** a counterexample to distance from the class of all admissible RN slices: these data belong to that equality class. Nor is it by itself a GH lower bound. The source already exhibits nonstatic/boosted equality slices; the high-frequency family makes the lack of a uniform tensor modulus explicit but is not nominated as a new finding.

### 1.2 The transport screen: the exact missing operation

Let BT denote *Sharp One-Third Stability of Brenier Maps*, September 25. Its source is uniform probability on a fixed compact convex body $K\subset B_R(0)$, with nonempty interior; targets are arbitrary probabilities in a fixed compact $Y\subset B_L(0)$, without convexity or density assumptions on $Y$. It proves the sharp exponent (1/3) for $L^2$ map distance versus $W_2$, uniformly in atom count, masses and site separations. The three-atom example on the cube has

$$
W_2=a^{3/2}/2,\qquad
\|T_\mu-T_\nu\|_2=\tfrac12\sqrt a\sqrt{1+a^2},\qquad W_1=a^2/2.
$$

It already obstructs improving the exponent in the proposed larger density class, since that class contains the constant density.

The operative new source input is the cell-moment estimate

$$
\sum_i\frac{|DB_i[q,0]|^2}{M_i}\le162R^2\sum_i\frac{|DM_i[q,0]|^2}{M_i}.
\tag{BT}
$$

Here $M_i$ and $B_i$ are masses and first moments of the affine-maximum cells, and $q$ changes the intercepts, with sites fixed. Knothe coupling of uniform laws on the two perturbed cells gives exact domination of the midpoint law by central-cell Lebesgue measure after multiplication by the geometric mean of the two cell masses. Applying $R^2-|x|^2$, summing over the partition, and cancelling endpoint terms gives a quadratic bound in the mass differences. The derivative limit is taken at a fixed finite configuration; its permitted step may depend on the smallest mass, but the final constant does not.

The finite-target proof uses an optimal target coupling to move paired sites linearly; cyclic monotonicity prevents interior collisions. A graph Laplacian solves $DM_i[q,0]=m_i c_i'$; no norm estimate on the solution $q$ is used. (BT) bounds the weighted intercept velocity, giving potential distance linear in $W_2$. Convex gradient interpolation, already attributed by the source to Delalande–Mérigot, gives the cube-root map bound. Repeated endpoint slopes merge; finite nets and strong $L^2$ convergence handle general targets. These limiting operations are already source premises.

For $c\le f\le C$, the same crude midpoint argument gives a multiplicative domination constant (C/c), not one. At zero perturbation the resulting inequality contains a nonzero $O(C/c-1)\int\Phi f$ slack. Dividing by the squared perturbation parameter does not yield (BT). This is a failure of this proof operation, not a counterexample to the density-weighted theorem. For log-concave $f$, the triangular Jacobian and log-concavity recover exact midpoint domination; that restricted extension is a direct reuse of the source mechanism and not a substantial target. For arbitrary smooth positive bounded $f$, a precise sufficient bridge is the weighted analogue of (BT), uniform in all finite configurations and independent of every derivative of $f$. I have not proved or disproved it.

Two-sided density comparison does suffice for the **subsequent** convex gradient interpolation. Thus adding a derivative-dependent elliptic estimate or rebalancing its exponent would miss the actual issue. A fixed finite configuration can be differentiated for smooth $f$; uniform passage through small cells/sites is exactly what cannot be assumed. If a bound uniform in smooth $c\le f\le C$ were established, bounded-density approximation and uniqueness of optimal plans would be the next limiting interface, not an excuse to skip it.

Primary comparison: [Letrouit–Mérigot, 2411.04908v3](https://arxiv.org/abs/2411.04908v3), Theorem 2.1 and its proof, already use density comparability with a log-concave reference, Brascamp–Lieb, tilted measures, and a global variance estimate; Proposition 2.2 supplies the convex gradient interpolation. Their variance estimate is not the uniform cell-moment inverse needed above. [Ruan, 2610.07577v1, October 6](https://arxiv.org/abs/2610.07577v1), Theorem 8 and the repairing proof in Sections 11–12, yield $W_1^{s/[2(1+s)]}$ for $f\in L^p$, $s=1-1/p$, including $W_1^{1/4}$ for bounded density. Repairing couples the target displacement into a cost deficit, then applies conditioning. This does not become $W_2^{1/3}$ by substituting $W_1\le W_2$. No duplicate or novelty conclusion is inferred from search results alone.

## 2. Selected Kerr target and exact dependency contract

Write K2 for *Generic Future Inextendibility with Square-Integrable Connection Near a Fixed Kerr Spacetime*, September 23; K1 and K0 for its C1 and quantitative C2 companions. The relevant source files and labels are in `contracts.json` and `source-manifest.json`. K2's full weak-exit, packet, nonlinear-comparison, attachment and holonomy proof interfaces were examined, including the companion amplitude contract and K0's actual high-current proof. They are premises, not results proved by this investigation.

Fix $M>0$, $0<|\mathfrak a|<M$, its complete two-ended Kerr bridge $\Sigma\simeq\mathbb R\times S^2$, reference $h_*,\nabla_*$, and a smooth $\rho\ge1$ equal to radial coordinate outside a compact set on each end. For symmetric covariant tensors $u,v$,

$$
p_m(u,v)=\sum_{j=0}^m\left(\sup_\Sigma\rho^{1+j}|\nabla_*^ju|_*+
\sup_\Sigma\rho^{2+j}|\nabla_*^jv|_*\right).
$$

The data space consists of smooth complete positive $h$, smooth $K$, finite $p_m(d-d_*)$ for every $m$, and the vacuum constraints. It has the relative topology of all these seminorms. Let $U_\epsilon=\{p_{10}(d-d_*)<\epsilon\}$. No parity, fixed asymptotic charge, fixed leading coefficient, or asymptotic expansion is imposed. Higher seminorms need not be small.

A future extension has a connected smooth time-oriented four-manifold, a continuous nondegenerate Lorentz metric, a smooth time-orientation-preserving isometric embedding of the **full** MGHD with proper open image, and a future timelike $C^1$ curve exiting it. No field equation or global hyperbolicity is required outside the image. For the target under investigation, lowered distributional Koszul coefficients, equivalently the weak coordinate derivatives of the metric, must belong locally to the Orlicz class

$$
\Phi_q(t)=t[\log(e+t)]^q,\qquad q=1.
\tag{O}
$$

Equivalence with the raised weak connection uses bounded metric/inverse on relatively compact charts and the identity $\partial_k g_{ij}=\Gamma^\flat_{i,kj}+\Gamma^\flat_{j,ki}$. Smooth chart transitions preserve this class: their derivatives and Jacobians are bounded on compact subcharts and $\Phi_q(Ct)\le C'\Phi_q(t)$. Pointwise a.e. derivatives without distributional derivatives are not enough. This class is contained in $W^{1,1}_{\rm loc}$, and contains every local $W^{1,p}$, $p>1$.

**Unproved target O1.** Does every fixed rotating subextremal center have some source-compatible $U_\epsilon$ in which data admitting such a future extension with $q=1$ form a meagre set? No positive answer is assumed. The investigation also tracks general fixed $q>0$ to expose the threshold calculation. It does not assert uniformity as $q\downarrow0$, $\mathfrak a\to0$, or $|\mathfrak a|\to M$.

### 2.1 What the source already pays for

The comparison wedge has

$$
g=-2a\,du\,dv+\gamma_{AB}(d\theta^A-b^Adu)(d\theta^B-b^Bdu),\quad
a=q_0e^{-\kappa(u+v)}\mathcal A,\quad t=(u+v)/2\ge0.
$$

Both optical orderings are available. The relative lapse and angular metric/inverses are uniformly nondegenerate with low angular bounds. There are envelopes $g_i(y_i)$ whose unit-cell suprema sum, controlling shape, lapse and shift coefficients and the specified first pure jets. At every **fixed** high order, ordinary jets on $u\le U,v\le CT$ are $Q_T=e^{o(T)}$. This means for every fixed $\delta>0$ a datum/order-dependent $C_\delta,T_\delta$ exists; it is not a polynomial bound and does not control the constants as $\delta\downarrow0$.

For finite full-lifetime timelike geodesics, K0 gives first comparison runout classification, and K1 removes the corner seeds as a null set. Branch tubes have bounded canonical momenta $p=-(\pi_u+bP)>0$, fixed position/angle margins, and a fixed launch footprint. The reduced Hamiltonian is $a(1+\gamma^{-1}PP)/(2p)$; its fixed state derivatives are $e^{-\kappa v}e^{o(v)}$, hence integrable. Canonical section volume is exact, including variable hitting time. Position projections need not be injective.

The packet construction provides exact smooth vacuum data on the **whole** bridge, preserving the other end, the connecting region and an expanding protected ball. The constraint correction has an allowed decaying exterior tail; imposing compact support or fixed charges would change the contract. For $A_T=e^{-\alpha T}$, $\lambda=e^{\zeta T}$, the linear hierarchy is homogeneous, constrained by the linearized Bianchi identity, and has a real trace-free angular polarization on the whole footprint with size at least $e^{-o(T)}$. K1's `prep:amplitude-independent-exterior` explicitly allows every fixed $\alpha>0$, ending at the entry cylinder.

K2 constructs an exact double-null template and controls its relative shift derivative using the torsion identity, not division of an uncontrolled shift error by the lapse. Its defects are bounded by

$$
A\lambda^{-N}e^{C_sT+o(T)}+A^2\lambda^{P_s}e^{o(T)}.
\tag{D}
$$

Here $s$ is a fixed base jet budget; the positive frequency powers are fixed **before** increasing inverse-frequency accuracy $N$. The $e^{C_sT}$ can occur when converting residuals into the null identities. The actual nonlinear comparison has uniform moving-family high bounds, a compensated low system, and error $e^{-(1+c)\alpha T}$ at each requested finite output order after choosing the finite budgets and losses. In particular, the angular Hodge loss $\sigma^{-1}Z$, $\sigma=\sqrt q$, is already compensated by factors $a$ or $\sigma h_i$. Rediscovering that compensation would not be a new bridge.

Whole-bridge attachment uses actual exterior collars, geometric uniqueness, protected compact shadows, and exiting sides. The resulting finite region embeds into the full MGHD. Its collar widths and persistence neighborhoods may depend on the fixed experiment time $T$. The source does not identify the whole MGHD with the comparison wedge or assert continuity of maximal lifetime.

On an observation box, put $r=e^{-\kappa T}$, $F=(\partial_u,r^{-1}\partial_v,\partial_{\theta^1},\partial_{\theta^2})$. The Gram matrix/inverse are bounded, ordinary jets are $e^{o(T)}$, volume density is comparable to $r$, and selected timelike velocities have bounded $F$-components. The original and persisted perturbed metric have matched numerical terminal states. Their curvature blocks $D_{AB}=R(\partial_v,\partial_A,\partial_v,\partial_B)$ differ by more than $A$ on $|\cos(\lambda v)|\ge1/2$.

## 3. Technical deduction: the same mechanism reaches every fixed $p>1$

This subsection is included so the genuine remaining target is not confused with a superficial extension. The deduction uses a different ambient integrability hypothesis, but no new structural operation beyond the source proof. It is **technical**, not the requested substantial finding.

### 3.1 Weak exits require only $L^1$ up to the chart norm budget

K2 `ex:homotopy` uses compact intrinsic diamonds and a causal homotopy with interior endpoints, and `ex:graph` constructs a local Lipschitz first-exit graph using only continuity and nondegeneracy. For small boxes around that graph,

$$
\int_{D'}\ell^{-3}\int_{Q_\ell(z)}|\Gamma|\,dx\,dz
\le C\int_{\mathcal L_\ell}|\Gamma|\,dx\longrightarrow0.
$$

The last step is $L^1$ absolute continuity since the graph has four-volume zero. This is where the printed proof uses $L^2\Rightarrow L^1$, and no stronger integrability is subsequently needed to extract the family. Smooth stopped geodesics, parameterized on canonical position–momentum sections, satisfy an exact Jacobian-one formula. The total connection integral over the initial family is $o(\ell^3)$, while its phase volume is comparable to $\ell^3$. Markov and the slope equation keep a positive portion inside the cone until its full endpoint. Fubini justifies weak/smooth connection agreement along almost every sampled arc. There is no trace claim on a prescribed curve.

The full arcs are then covered by finitely many charts with metric/inverse bounds, velocity bounds and interior margins. If the ambient metric is $W^{1,p}$, take the chart $L^p$ budget instead of $L^2$. If it satisfies (O), use the chart modular budget instead. The full-MGHD classification, corner-null argument and rational seed-ball density point step remain the same. Tube geometry is an existential witness; only the seed basis and integer chart budget are countable indices.

### 3.2 A general $L^p$ stopped-loop estimate

Rectangles have displacements $\ell\partial_v,\ell rX,-\ell\partial_v,-\ell rX$, where $X\in\{\partial_1,\partial_2,\partial_1+\partial_2\}$. In the $F$-frame their velocities are $O(\ell r)$. Select the least good ambient chart, and stop when the frame matrix $M$ reaches a fixed bound or chart displacement reaches half the margin.

The bounded timelike velocity is essential for the base comparison. The positive definite form

$$
K(G,U)=G+2(GU)(GU)^t,\qquad\det K=-\det G,
$$

bounds $M,M^{-1}$ in both frames. Bounded Lorentz Gram matrices alone would allow unbounded boosts.

At a fixed edge parameter, translation of observation positions is injective and independent of the bounded momentum labels. Isometry plus the volume density, not an assumed derivative bound for $M$, gives $dx\le C r^{-1}dy_{\rm chart}$. Thus Jensen on the unit edge and integration over positions/momenta yield

$$
\int I_e^p\,d\nu\le C/r,\qquad
\nu\{I_e>R\}\le C/(rR^p).
\tag{P1}
$$

There are only finitely many sampled edges and loop sizes. Momentum-dependent chart selection and stopping only restrict nonnegative integrals. Fubini removes exceptional connection representatives before the smooth transport ODE is used.

The exact frame equation is $M'=M\mathsf A-\widetilde\Gamma(Mf)M$. Scaled Koszul coefficients satisfy $|\mathsf A|\le\ell Q_T$. On the good parameters,

$$
\|M-M(0)\|\le C(\ell Q_T+\ell rR),\quad
|y-y(0)|\le C\ell r.
$$

If these tend to zero, continuity rules out the first stop and chart holonomy obeys $\|H(j\ell)-I\|\le C\ell rR$, $j=1,\ldots,17$. The source's eighteenth-jet bound and fixed Vandermonde inversion then give

$$
|D|\le C rR/\ell+Q_T\ell^{16}.
\tag{P2}
$$

The identification is exact: the quadratic loop coefficient is $R(\partial_v,rX)$ in $F$, and pairing it with $F_1=r^{-1}\partial_v$ cancels the factor $r$. Three angular directions recover the symmetric block.

Fix $p>1$, set $t_p=1-1/p>0$, and choose

$$
a=b=\delta=t_p/4,\qquad A=r^a,\quad \ell=r^b,\quad R=r^{-1/p-\delta}.
$$

Then the exceptional measure is $O(r^{p\delta})\to0$, the frame stop terms tend to zero since $b>0$ and $b+t_p-\delta=t_p>0$, and

$$
|D|\le C r^{t_p/2}+Q_T r^{4t_p}=o(r^{t_p/4})=o(A).
\tag{P3}
$$

The algebra works arbitrarily close to $p=1$, but no constants or times are uniform there. Keeping the printed amplitude $a=1/4$ and merely replacing Cauchy–Schwarz would create an artificial threshold; the source's amplitude-independent operations must be reused first.

### 3.3 Checking the amplitude change through the actual nonlinear proof

Take $\alpha=\kappa a\in(0,\kappa/4)$, fixed before $T$. K1 gives the general-amplitude exterior construction. K2's interior proof also goes through, for the following explicit reasons.

1. Its bootstrap envelope is $g_i+e^{-\alpha T/2}\psi_{i,T}$. The added mass/cell-supremum sum is $O((T+1)e^{-\alpha T/2})$, and its tails are uniformly tight because 
   $\sup_{T+1\ge R/C}(T+1)e^{-\alpha T/2}\to0$. No fixed lower bound for $\alpha$ is used.
2. In the high-current proof, equal multipliers on paired angular currents preserve cancellation. Auxiliary-current rescaling, a tail threshold, and fixed-direction damping are chosen in that order. All losses can be made $e^{\eta T}$ for an arbitrary **fixed** $\eta>0$. Recovery uses the bounded directional potential and does not divide the weighted curvature energy by the small lapse.
3. The low difference system has only the limiting arrows $(Y_i,N_i,z_i,D_b)\to P$. Its good-region growth can be made arbitrarily small. Late support confines bad slices to total length $t_0+\nu T/2+O(1)$. Hence the exact same proof gives $L^2$ error $A^2e^{\eta_2T}$, with $\eta_2$ chosen as a sufficiently small fraction of the new $\alpha$.
4. Fix the target derivative order $s\ge30$, a spatial order $k\ge2s$, then an interpolation order $M\gg k+2$ so $2(1-(k+2)/M)>1+c_1$, $0<c<c_1<1/2$. Fix the finite input buffer. Choose all losses, current multipliers, tail thresholds, support fraction, and exterior tolerances. Next choose $\zeta>0$ small enough for **all** positive frequency powers and $(m+5/2)\zeta<\alpha$. Only then increase inverse-frequency accuracy so the first term of (D) fits below the quadratic error. Finally take $T\to\infty$ along the admissible branch sequence.
5. Interpolation gives $C^s$ error $e^{-(1+c)\alpha T}$. Time recovery uses at most two spatial derivatives per time derivative and no inverse lapse. The template change is $o(e^{-\alpha T/2})$, so the bootstrap improves. At each fixed $T$, positive lapse and finite norms allow the existing smooth restart; its time need not be uniform in $T$.

The packet curvature signal remains larger than $A$: its leading term is $-A\lambda^2\cos(\lambda v)(p_0)_{AB}/2$, the screen lower bound is $e^{-o(T)}$, and the finite error hierarchy has been chosen with strict exponential margins. Attachment and matched-seed persistence concern a fixed experiment and survive this change. The neighborhood $U_\epsilon$ need not shrink with $p$; sufficiently late perturbations enter the same low-order neighborhood. A single packet sequence need not tend to zero in **all** $p_m$ at once: density is tested in an arbitrary but fixed finite-seminorm neighborhood, exactly as in the source.

Finally, for each extension test $E_p(O,B)$, assume it is dense in some open set, pick an extendible background there, construct its exact perturbed datum in that finite neighborhood, and use density to select a persisted extendible datum close to the fixed experiment. Canonical section volume leaves more than $0.91\mu(O)$ jointly good parameters on every observation slice; the oscillatory good times occupy more than half the fixed interval. The exceptional measures in (P1) tend to zero. At a remaining parameter (P3) makes both curvature blocks $o(A)$, contradicting their difference $>A$. Thus each test is nowhere dense, and the exit cover gives meagreness for the specified $p$. A countable sequence $p_j\downarrow1$ and local inclusion can give a common residual subset if desired; that standard intersection is not a new mechanism.

## 4. The logarithmic target: two constructive attacks and where each fails

### 4.1 Averaging is not the missing part

For a chart with $\int\Phi_q(|\Gamma|)\le B$, convexity and the same stopped translation argument give

$$
\int\Phi_q(I_e)\,d\nu\le C/r,\qquad
\nu\{I_e>R\}\le C/[r\Phi_q(R)].
\tag{O1}
$$

For fixed $0<\delta<q$, take $R=r^{-1}T^{-q+\delta}$. Since $\log R\sim\kappa T$, the exceptional measure is $O(T^{-\delta})$, while $rR\asymp T^{-q+\delta}$. Coefficient extraction would give

$$
|D|\le C T^{-q+\delta}/\ell+Q_T\ell^{16},
\quad\text{provided}\quad \ell Q_T\to0.
\tag{O2}
$$

No choice of the source's fixed exponential $A=e^{-\alpha T}$ and exponential loop size can turn the first term into $o(A)$. A polynomial loop $\ell=T^{-b}$ would instead require polynomially controlled loop jets and a polynomially visible signal. Merely knowing $Q_T=e^{o(T)}$ does not suffice: $Q_T=e^{\sqrt T}$ satisfies every source subexponential bound and defeats every such loop scale.

These inequalities are an exact limitation of the current argument, not proof that O1 is false. At $q=0$, (O1) only gives the $L^1$ cutoff loss $rR\to\infty$ if the exceptional measure is forced to zero. Absolute continuity for one fixed chart can give datum-dependent refinements, but the density argument compares moving witnesses. Their bounded modulars do not supply a uniform absolute-continuity modulus.

### 4.2 Constructive approach A: replace exponential damping by polynomial propagation

I attempted to use the actual triangular current graph, not a black-box Gronwall bound. The favorable trace equation is

$$
(L_i+\kappa)(\tau_i/\mathcal A)=-\mathcal A^{-1}|\chi_i|^2.
$$

The source already uses its exponentially damped convolution and a bounded potential $\Phi$ with $L_i\Phi=h_i$ to absorb Volterra terms $\int h_iP$. That removes growth in the final recovery step. It does **not** remove the $e^{\eta T}$ loss in the paired high fluxes used as its input. K0's `in:higher` proof and K2's moving-family version both first rescale the triangular limiting arrows by fixed small multipliers, then remove a weight $e^{-2\eta(u+v)}$. The resulting constants depend on $\eta$, and the tail threshold is selected after the multipliers. Setting $\eta=(\log T)/T$ would change those thresholds and fixed-region losses with $T$; the proof does not bound them.

A non-geometric diagnostic isolates why “integrable return coefficients plus triangular limiting graph” cannot, alone, fix this. For $t\ge8$, let

$$
P(t)=e^{t^{1/3}},\quad Y=P',\quad
h(t)=P''/P=\tfrac19t^{-4/3}-\tfrac29t^{-5/3}\ge0.
$$

Then $P'=Y, Y'=hP$, $h\in L^1([8,\infty)$), its cell suprema sum, and the zero-$h$ system is triangular. Nevertheless $P$ exceeds every polynomial. Smooth positive extension of the coefficients on an earlier compact interval is harmless. This is an exact counterexample to the proposed **abstract estimate**, not a vacuum spacetime or a counterexample to the more structured source equations. It says the remaining tensor/directional structure must actually be used to eliminate or better weight the return interaction.

The source contains more low-tail information than the headline $\ell^1$ envelope. K0 `co2:levels` fixes the squared trace weight $A_S=1.06$; `in:entry` derives cell sequences with $\sum\langle n\rangle^{1.06}a_n^2<\infty$. Weighted Cauchy–Schwarz gives $\sum\langle n\rangle^q a_n<\infty$ for $q<0.03$. It does **not** give the first moment. Propagating even those small moments through the two-direction low system requires a weighted version of the source proof; it is not silently asserted here. In particular a claim of generic nonextension in every arbitrarily small logarithmic class would need to confront this retained input. The selected test is $q=1$, not such a blanket claim.

There is a second obstruction before one reaches the holonomy estimate. With polynomial amplitude and frequency $A=T^{-a},\lambda=T^z$, the linear conversion term in (D) is $T^{-a-zN}e^{C_sT+o(T)}$. No fixed accuracy $N$ absorbs a positive $C_sT$. Increasing accuracy with $T$ is not authorized by smooth fixed-order bounds: the hierarchy constants, background jets and beam errors have no uniform analytic/Gevrey control in that limit. Thus a polynomial-current improvement alone would still leave a gauge/residual conversion problem.

Even an ideal polynomial package would have to quantify the launch cost in the **actual** $p_m$ topology. The existing estimate is a polynomial-in-$T$ factor times $A\lambda^{m+5/2}e^{o(T)}$. Exponential amplitudes absorb this for every fixed $m$. For polynomial amplitudes its degree matters and cannot be suppressed as “harmless”; arbitrary finite neighborhoods may require arbitrarily large $m$. If a future proof gave $Q_T\le CT^K$, the simple eighteenth-jet approach would at least need

$$
b>K,\qquad 16b>K+a,\qquad a+b+\delta<q,
$$

as well as convergence of the exact constrained initial perturbation at the requested $m$. These are diagnostics for a missing construction, not hypotheses added to O1. No such construction was obtained.

### 4.3 Constructive approach B: observe finite-frequency holonomy directly and use signed packets

The coefficient extraction loses $1/\ell$ and asks for high jets. I therefore tested observing a packet-scale rectangle $\ell\asymp\lambda^{-1}$ directly, with phase chosen on a positive fraction of the fixed observation interval. The leading curvature is $A\lambda^2$, so a genuinely controlled direct loop signal would be of order $A$, instead of extracting its quadratic coefficient from eighteen values. The ambient bound would be of order

$$
\ell rR\asymp T^{-q+\delta}/\lambda.
$$

At this formal level the necessary inequality is $A\lambda\gg T^{-q+\delta}$. For the source's exponential packet, convergence in the chosen finite $p_m$ neighborhood requires $\alpha>(m+5/2)\zeta$ after reserving the other losses, so $A\lambda=e^{-(\alpha-\zeta)T}$ is exponentially small. It cannot satisfy that inequality. The curvature factor $\lambda^2$ therefore does not solve the logarithmic scale mismatch.

I also checked the K1 signed $+A/-A$ preparation: its odd comparison cancels even exterior errors and has a cubic remainder with arbitrarily small fixed exponential loss. Using it to cancel nonlinear terms at a finite number of further orders would still leave $A^k e^{\eta T}$ for fixed $k,\eta>0$, which is not small relative to a polynomial $A$. Taking $\eta$ or the order to depend on $T$ again lacks uniform constants. Further, a direct-loop lower bound needs a common gauge and control of background transport/noncommuting curvature across the loop. The source's pointwise curvature **difference** is not already such a lower bound. I do not assert the formal order-$A$ direct-loop signal as a proved lemma.

Broad, low-frequency incoming packets might reduce the radial weights paid by a short high-frequency launch. They would change the fixed-footprint oscillatory signal and matching construction; no admissible whole-bridge realization with the requisite uniform visibility was produced. This is an identified alternative, not a generic proposal counted as success.

## 5. Geometric counterexample attempts at the lower endpoint

### 5.1 A local $W^{1,1}$ extension follows from the comparison-wedge bounds

This is a local statement about a wedge near a branch, not a full-MGHD extension theorem. Fix a compact $u$-interval and angular patch, and set $V=-e^{-\kappa v}$. Then

$$
g=-2(q_0/\kappa)e^{-\kappa u}\mathcal A\,du\,dV
 +\gamma_{AB}(d\theta^A-b^Adu)(d\theta^B-b^Bdu).
$$

The source identities give $\partial_v\gamma=2\chi_1$, $\partial_v\log\mathcal A=\ell_1+\kappa$, $\partial_vb=q\mathcal A\gamma^{-1}(\xi_1-\xi_0)$. Their suprema are integrable in $v$ on this patch, using $g_1\in L^1$ and $q=O(e^{-\kappa v})$. Hence all three fields have uniform limits as $V\uparrow0$. Their tangential first derivatives are bounded by the low package; their limits are tangentially Lipschitz. Since $dV=\kappa e^{-\kappa v}dv$,

$$
\int|\partial_V\gamma|\,dV=\int|\partial_v\gamma|\,dv<\infty,
$$

and similarly for $\mathcal A,b$. The limiting angular matrix and relative lapse remain nondegenerate. Constant continuation of their boundary values to $V\ge0$ gives a continuous nondegenerate Lorentz metric in $W^{1,1}_{\rm loc}$; continuity removes any distributional jump measure. A small straight timelike curve can cross $V=0$ because the $du\,dV$ coefficient stays nonzero.

A sufficient condition for $L\log^q L$ in this chart is $\int(1+v)^q g_1(v)dv<\infty$: the unscaled first derivatives are bounded, so their logarithmic amplification after dividing by (dV/dv) is at most (C(1+v)). No such first-moment conclusion is asserted from the inspected package. The comparison wedge is only an open region of the full MGHD, and its boundary may already be interior to that MGHD. Hausdorff gluing and the full-exit condition are separate requirements. Consequently this construction does not refute the technical generic $p>1$ deduction and does not prove global sharpness at $p=1$.

### 5.2 Exact smooth vacuum metrics with adjustable logarithmic thresholds

Here the objects are actual smooth interior vacuum metrics, not abstract stress measures. Let $V\in(-\varepsilon,0)$, $L=\log(1/|V|)$, $a>0$, and $\beta(V)=cL^{-a}$, $c>0$. Choose $\varepsilon<e^{-2}$ and $c$ so that

$$
I=\int_{-\varepsilon}^0|s|\beta'(s)^2ds
=\frac{c^2a^2}{2a+1}[\log(1/\varepsilon)]^{-2a-1}<1/4.
$$

Solve $y''=-\beta'^2y$, $y(-\varepsilon)=1,y'(-\varepsilon)=0$, on the open interval. The Volterra formula is

$$
y(V)=1-\int_{-\varepsilon}^V(V-s)\beta'(s)^2y(s)ds.
$$

Until a hypothetical first zero, concavity gives $y\le1$, and $V-s\le|s|$ gives $y\ge1-I>3/4$. Thus there is no zero, these bounds hold throughout, and the decreasing $y$ has a positive limit at zero. Moreover $\int|y'|<\infty$, either by monotonicity or Tonelli in the formula for $y'$.

On a product coordinate patch define

$$
G=-2\,du\,dV+y(V)^2\{e^{2\beta(V)}dx^2+e^{-2\beta(V)}dz^2\}.
\tag{R}
$$

It is smooth Lorentzian for $V<0$. If $p=ye^\beta$, $s=ye^{-\beta}$, direct computation gives the only possibly nonzero Ricci component

$$
\operatorname{Ric}_{VV}=-(p''/p+s''/s)
=-2(y''/y+\beta'^2)=0.
$$

In particular it is Ricci flat, not merely a tensor satisfying an abstract divergence constraint. The relevant Christoffel coefficients are

$$
\Gamma^x_{Vx}=y'/y+\beta',\qquad
\Gamma^z_{Vz}=y'/y-\beta'.
$$

All other nonzero coefficients are bounded multiples of $y',\beta'$. Their difference $2\beta'$ prevents cancellation of the singular part. Constant continuation of $y,\beta$ at $V=0$ gives a continuous nondegenerate $W^{1,1}$ metric across that hypersurface, with a timelike crossing curve.

To compute the exact logarithmic threshold, write $x=|V|$. Then

$$
|\beta'|=ca/[xL^{a+1}],\qquad
|y'|\le C/[xL^{2a+2}]+C.
$$

The latter bound follows by integrating $\beta'^2$ and differentiating $1/(xL^{2a+2})$ for large $L$; its derivative is comparable to $-1/(x^2L^{2a+2})$. Thus $y'/\beta'\to0$. Also $\log(e+|\beta'|)\sim L$. On every bounded transverse box,

$$
\Gamma\in L\log^qL\quad\Longleftrightarrow\quad
\int^{\infty}L^{q-a-1}dL<\infty
\quad\Longleftrightarrow\quad q<a.
$$

At $q=a$ the integral diverges logarithmically. For every $p>1$, $\int|\beta'|^p\,dV=\infty$. The implication from the difference of two coefficients to failure of the whole array uses the elementary doubling inequality for $\Phi_q$. The contribution from $y'$ has the weaker restriction $q<2a+1$, so does not change the threshold.

For example $a=1/2$ gives a canonical $W^{1,1}$ continuation with no $L\log L$ connection; $a=2$ gives an $L\log L$ continuation but no $W^{1,p}$ continuation in this displayed chart for any $p>1$. These are **not** claimed to be near-Kerr complete-bridge data, nor do canonical-coordinate failures rule out all other smooth extension structures. They show that vacuum, continuous nondegeneracy and directional $L^1$ control alone do not determine a logarithmic threshold. Any resolution of O1 must use the global data/tail mechanism and arbitrary-chart observation, not those three properties alone.

## 6. Current primary comparison for the selected route

All versions below were freshly retrieved as bytes on October 9, 2026; the final submission-history check prompted retrieval and reading of Dong v4, Letrouit–Mérigot v3, and Luk v3 in addition to the initially read older versions; HTTP status, versioned URL, headers, byte count, SHA256, extraction hash and failed requests are retained. Search responses are discovery aids, not evidence of novelty. The exact read passages are logged; fetched-but-unread portions are not represented as verified proof dependencies.

* [Cameron–Sbierski, 2609.05167v1](https://arxiv.org/abs/2609.05167v1): Theorem 1.1 excludes strongly spherically symmetric $C^0\cap W^{1,s}$, $s>1$, extensions locally equivalent to a reference continuous boundary, under divergence of the integrated infimum of $|\partial_vr|^s$ on every sufficiently small transverse interval. Its proof uses the invariant area radius, cone-coordinate derivative dominance, volume/Jacobian comparison and Hölder to prevent cancellation. Removing boundary equivalence in its applications requires further geometric rigidity. This is not the nonsymmetric full-MGHD weighted-topology statement above; conversely, replacing its symmetry requirement is not accomplished by merely citing the theorem.
* [Sbierski, 2409.18838v2](https://arxiv.org/abs/2409.18838v2): Theorem 3.14 is a Lipschitz obstruction using signed integrated curvature blow-up robust under perturbation of continuous testing fields, together with its connection/shift bounds. It does not by itself replace an arbitrary $L\log L$ chart modular by a trace along a chosen path.
* [Luk–Sbierski, 2604.04877v1](https://arxiv.org/abs/2604.04877v1): Theorem 1.2 uses characteristic data with event-horizon upper bounds, a weighted averaged lower bound in the $l=2$ dynamical Teukolsky modes and improved auxiliary bounds. Theorem 4.38 supplies the robust integrated curvature obstruction used for Lipschitz inextendibility; Proposition 4.40 retains integrable null connection control. These tail assumptions cannot be silently supplied for every datum in K2's weighted neighborhood. The inspected theorem/proof interfaces do not supply a logarithmic chart-invariant conclusion.
* [Luk, 1311.4970v3](https://arxiv.org/abs/1311.4970v3): Theorems 2–4 allow characteristic singular profiles controlled by functions with integrable inverse square, construct smooth interior vacuum metrics with continuous boundary extension, and prove non-$L^2$ Christoffel coefficients in the construction's coordinates under divergence along Lebesgue-almost every initial null generator. The paired weighted curvature integration retains the weight derivative in the favorable direction and renormalized curvature variables. This is relevant nonlinear machinery, already demonstrating that weak null singularities can have only $L^1$-type connection control. The paper explicitly distinguishes coordinate non-$L^2$ from exclusion of every extension. It does not close the whole-bridge launch/regularity problem here.

The Dafermos–Luk version 1710.01722v1 was retrieved as a companion reference, but no new conclusion in this report relies on an unexamined passage of that long paper. The stronger stipulated K0/K1/K2 interfaces, including their proofs, are the evolution premises used. The all-$p$ deduction above is therefore not promoted on the basis that no exact statement was located externally. Its operation-level overlap with the source is the affirmative reason for classifying it as technical.

## 7. Remaining mathematical work and significance disposition

O1 is a precise investigated gap. The source already supplies arbitrary weak-exit families, exact full-bridge constraint solves, global attachment, moving-family nonlinear comparison, boost control, canonical parameter matching, finite persistence and arbitrary-chart stopped averaging. The unresolved operation is not one of these under a new name.

A successful nonroutine route would have to supply polynomial/logarithmic visibility compatible with arbitrary finite weighted data neighborhoods, and propagate it with error small relative to that visibility through the actual Einstein gauge/constraint system. Approach A failed both at polynomial high-current control and at the inverse-lapse linear residual conversion. Approach B avoided formal coefficient extraction but failed at signal size versus weighted launch smallness, and did not prove a robust direct holonomy lower bound. Extra weighted decay sufficient for an extension must also be tracked: one cannot merely assert that more logarithmic regularity is generically impossible.

No compactness theorem with a desired conclusion inserted as an assumption was used. There is no claim of a new Penrose inequality obtained by algebraic combination, no claim that equality implies stability, no abstract stress recovery claim, and no numerical proof. The smooth RN and Rosen constructions state exactly which stronger statements they refute and which they do not.

I27 remains parked with its divergent borderline center integral, absent flat-scale/center-mass retention and shrinking-core scalar-square loss; positive hyperplane-concentrated stresses still prevent recovery from limiting stress equations alone. I30's final mathematical PASS and **technical-only significance** are preserved: Clarke's measurable-subset volume bound and Tian–Wang's stopping/packing operations already pay for its mechanism. Unequal sphere products still refute the proposed universally attracting normalized Einstein flow; no preservation of nonnegative sectional curvature under four-dimensional Ricci flow is assumed. I29 and I31 are untouched.

This report does not meet the bar of a new mechanism paying a previously unpaid deficit in the sense of the R011 benchmark. The appropriate handoff is the developed gap and the exact technical lemma, not an increment to the findings ledger or a priority claim.

## 8. Reproducibility and provenance

Paths are relative to the project root. `frontier/experiments/i32_geometric_relativity_discovery/verify.py` checks the artifact seal, frozen inputs, pinned selected-source hashes/Git blobs, exact logged passage hashes, primary retrieval bytes/extractions and the complete reused 9340-file corpus. It reports live shared-input drift separately from frozen integrity. `diagnostics.py` performs deterministic rational checks of the $p\downarrow1$ scale margins, the full Ricci array of the Rosen metric at 72 exact jets, the connection difference, the triangular-majorant coefficients and the RN curvature growth formula. The analytic proofs above, not those finite checks, establish the universal identities and integral thresholds.

The initial search-response archive did not retain its request object; this limitation is recorded instead of reconstructing a purported exact request. Subsequent query objects and responses are retained, including the final fresh three-topic check. Failed arXiv 1109.2165v2 requests are preserved as HTTP 404 bytes; v1 succeeded. A missing optional SymPy installation was handled by using standard-library rational arithmetic. No dependency installation or other-project write was required.

The verifier's first run rejected fourteen URL strings containing percent-encoded parentheses in the CAT(0) manuscript paths, although their file and Git hashes all matched. The initial output is retained. URL comparison was corrected to decode the path spelling before comparison; no source manifest or corpus byte was changed.

The frozen ledger and the final I30 review have different update times: the ledger captured older review-running text while the final review already gives technical-only significance. `live-drift.json` classifies later shared-file changes by hash. Such drift is not an artifact-integrity failure, and no attempt was made to repair the shared ledger. The parent retains integration and any separately authorized project-only publication.
