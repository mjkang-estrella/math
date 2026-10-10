# I126 — Original I123 audit and random-geometry discovery

**Original I123: PASS without repairs for A1, the exact-constraint heavy-tail example and its finite-time persistence, and B1–B5, with the method restrictions stated below. The I120 independent passes and the I117/I114 inherited passes are preserved, not reissued as fresh audits. Thermal Target B remains unproved and unrefuted, and parked. No substantial finding is nominated. Eight accepted findings remain eight.**

The new investigation selects the joint curve/occupation-measure limit for fixed weakly disordered FK-Ising in a square. It does not prove that target. It proves an exact quenched-mark replacement criterion and a whole-configuration entropy estimate which closes the shrinking-disorder regime, including the actual discrete counting measure. These are paid technical partials. Neither is passed off as a fixed-disorder theorem.

This is an independent AI proof audit and author-level mathematical investigation. It makes no human-review, formal-certification, or worldwide-priority claim. All pinned OpenAI theorems **and lower operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. External literature is not stipulated. No upstream truth audit, contradiction/ex-falso argument, child agent, shared edit, staging, commit, or publication was used. Active I124/I125 outputs are not dependencies.

## 1. Original objects, inheritance, and audit conventions

The frozen original I123 report is `frontier/iterations/i123-thermal-production-stability.md`, SHA-256 `3811dd6bfbc30da3543c06b7b803fbc438d4642150be13bffeb821eb2758c659`; its original seal is `6637f83d73e1270a4d7b5b61d5d1596859e273b4bb10b9ba771c29f596759756`. The finalized parent receipt is frozen byte-for-byte. The required complete original task JSON has SHA-256 `c0a4216b88cf7bde8e7ff4517c0d4fb2144e5457d1ab57fc5315f1d739653172`. All its decoded fields were read, including its 602-line brief through the ending. Its explicitly required recursive I120 task record, SHA-256 `d1b09ad8939c4842ddba3c672336e31f52ea6b0ec0433ac6e0ace2cbacad292d`, was read in full: the 1,011-line decoded brief and other fields. This preserves the supplied original briefs, reports, parent responses, objections, and earlier required record. Neither a summary nor the parent's selected checks substitutes for this audit.

The original I120 independent no-repair passes retained here are W120/W1–W6 for arbitrary centered finite-energy input; M120 with its exact constraint scope and double-log thresholds; M3; D1–D3 including Stieltjes continuity and endpoint conventions; D4 with arbitrary internal entanglement; the *conditional* production implication with its premise still unpaid; nonconvexity and the scoped Hessian diagnosis; and D5–D9, including actual entropy repair, discrimination, two-sided deficit, and trace asymptotics. Their disposition remains technical. I117's inherited passes are L1–L2, T1–T7 at their stated scopes, R1–R2, F1–F2, finite-energy/finite-memory-entropy conditional linear qEPI including continuous labels and heat endpoints, U117, and its noisy consequence. I114's B114, Q114, scoped counterexamples, endpoint results, and synthesis assessment retain their exact original scope. This report does not claim to have newly audited every old proof. In particular, there is no resurrection of a weighted-Q or ordinary-R stability bound, general stationarity, or bounded inverse attenuator.

For the original I123 audit use nats and the unhalved quantum trace norm. Put

\[
g(x)=(x+1)\log(x+1)-x\log x,\quad h(x)=\log(1+1/x),\quad
\tau_x=(x+1)^{-n}e^{-h(x)N}.
\]

The original data have finite integer \(n\ge2\), \(E>nr\), positive unequal \(r,b\), \(0<\eta<1\), centered arbitrary \(n\)-mode \(\rho\), \(S(\rho)=ng(r)=H\), and \(e=\operatorname{Tr}\rho N\le E\). Internal entanglement is unrestricted and the physical bath is independently \(\tau_b\). All the original same-input factorization parameters, including \(t\in(0,1)\), \(T=-\log t\), and \(\delta=S(T_{t,r}\rho)-H\le\Delta/\kappa\), remain exactly those in I123 §1. Varying an auxiliary bath below does not vary the physical bath.

## 2. Independent audit of the original paid I123 claims

### A1 — continuous BV decomposition: PASS without repairs

Let \(P_v=T_{e^{-v},r}\), \(x(v)=g^{-1}(S(P_v\rho)/n)\), and \(V=E/n>r\). Finite-energy entropy continuity and the exact energy evolution apply uniformly on each compact time interval, including zero. EPnI first gives \(r\le x(v)\le V\), and then

\[
x(v+a)\ge r+e^{-a}(x(v)-r)\quad(a\ge0).
\]

Thus \(Y(v)=e^v(x(v)-r)\) is continuous, nondecreasing, and zero at zero. On every compact interval it is bounded, so \(\nu=dY\) is a finite positive atomless Stieltjes measure. As in inherited D1, assign no atom at zero; integrals over \([0,T]\) use that convention. These statements do not assume an entropy derivative or absolute continuity. The product rule for continuous BV functions gives

\[
dx=(r-x)\,dv+e^{-v}d\nu.
\]

Set \(f=n(g(x)-g(r))\). The thermal relative-entropy identity, with the exact channel energy, gives

\[
F(v)=e^vD(P_v\rho\Vert\tau_r)=h(r)(e-nr)-e^vf(v).
\]

Consequently \(\mu=-dF=d(e^vf)\). The chain rule has no jump correction because \(x\) is continuous, and \(g\) is \(C^1\) on the positive compact interval \([r,V]\). It follows that

\[
d\mu=nh(x)d\nu+e^v k_r(x)\,dv,\qquad
k_r(x)=n\{g(x)-g(r)+(r-x)h(x)\}.
\]

Differentiating this *scalar* function gives
\(k'_r(x)=n(x-r)/[x(x+1)]\). Integrating from \(r\) proves both original bounds

\[
\frac{n(x-r)^2}{2V(V+1)}\le k_r(x)
\le\frac{n(x-r)^2}{2r(r+1)},\qquad h(V)\le h(x)\le h(r).
\]

All signs and factors of \(n,e^v\) agree. Since \(f(0)=0\),
\(e^vf(v)=\mu([0,v])\); positivity yields \(0\le f(v)\le e^{T-v}\delta\) for \(0\le v\le T\). The integrated original A1 is therefore exact, including any singular continuous mass. It retains \(I_r-D\) when that density exists; it never replaces it by \(I_r\).

Its noncoercivity discussion also passes at its stated scope. The scalar \(k_r\) term vanishes at time zero for every state on the entropy slice. The identity
\(D_v=h(r)e^{-v}(e-nr)-f(v)\) retains an uncontrolled nonnegative energy excess. A1 alone supplies neither a lower trace-power bound for \(\nu\) nor small input energy excess. This identifies the missing implication; it does **not** prove that no such implication can hold by a different argument.

### Exact-constraint heavy tail and OU persistence: PASS without repairs

With \(\mathbb P(J=j)=Cj^{-3}\), the first moment and Shannon entropy are finite, whereas the second moment is infinite. For independent uniform \(U\in\{0,\ldots,m-1\}\), the encoding \(K=mJ+U\) is injective, hence \(S(K)=S(J)+\log m\). Choose finite \(m\) making this exceed \(H\). The Fock-diagonal state \(\zeta\), supported in the first mode with the others vacuum, is centered and has finite energy and entropy but infinite \(N_1^2\) expectation.

For \(\rho_x=(1-\epsilon)\tau_x+\epsilon\zeta\), concavity gives \(S(\rho_r)>H\). The binary mixture upper bound gives
\(S(\rho_{r/2})\le ng(r/2)+\epsilon S(\zeta)+h_2(\epsilon)<H\)
for sufficiently small fixed \(\epsilon>0\). Independently impose \(\epsilon e_\zeta<E-nr\). Entropy is continuous in \(x\in[r/2,r]\) under the common finite-energy cap, so an actual root lies strictly between the endpoints. The resulting state is faithful, centered, has entropy exactly \(H\), energy below \(E\), and infinite second number moment. No finite-support approximation is substituted for this state.

For an individual first-mode Fock input the beam-splitter expansion against the independent thermal bath gives

\[
\mathbb E N'_1(N'_1-1)
=q^2\mathbb E N_1(N_1-1)
+4q(1-q)r\mathbb E N_1+2(1-q)^2r^2.
\]

The bath has zero anomalous contractions. The resulting terms are nonnegative, so summing over the input number distribution uses monotone convergence of nonnegative sums, not an unbounded cyclic trace identity. Every \(q=e^{-v}>0\) retains the infinite first term. The conclusion holds at **every finite** OU time; the limiting thermal state at infinite time is not a contradiction to it. The example excludes a general claim that positive time supplies finite fourth quadrature moments/high number moments. It does not assert undefined entropy production, failure of A1, or an all-power counterexample to Target B.

### B1 — variable auxiliary instrument: PASS without repairs

For \(y>0\), \(B=2y+1\), the balanced auxiliary channel prepares shifted copies of \(\tau_y\). On the vacuum vector the inverse quadratic form is

\[
\langle0|(D(z/\sqrt2)\tau_yD(z/\sqrt2)^*)^{-1}|0\rangle
=(y+1)^n e^{|z|^2/(2y)}.
\]

For a positive faithful operator \(A\), \(A-c|0\rangle\langle0|\ge0\) when \(c\le\langle0|A^{-1}|0\rangle^{-1}\); this follows by Cauchy–Schwarz in the \(A\)-quadratic form. Here the displayed inverse expectation is finite, so the original positive subtraction is legitimate. Its complement is a CP measure-and-prepare kernel. The heterodyne radial integral in number state \(k\) is \((1+1/(2y))^{-k-1}\). Tensoring gives exactly

\[
G_y=g_yq_y^N,\quad q_y=\frac{2y}{2y+1},\quad
g_y=[(y+1)(1+1/(2y))]^{-n}.
\]

In particular \(0<G_y\le g_yI<I\). The inverse of the branch-zero filter is bounded; the inverse of the branch-one filter \(\sqrt{G_y}\) is bounded only on the finite-number projection. Its squared cutoff norm is

\[
C_{y,L}=g_y^{-1}q_y^{-L}=[(y+1)(1+1/(2y))]^n(1+1/(2y))^L.
\]

At \(y=1/2\) it is \(3^n2^L\). There is no missing vacuum or half-photon factor and no global inverse-filter assertion. Li's underlying construction already allows a temperature greater than one; the parameterization and quantitative constant are a specialization of that operation.

### B2 — information loss, filtered reference, and tails: PASS without repairs

The different-pair doubling identity is applied to the independent port groups \((\rho,\tau_r)\) and \((\tau_B,\tau_B)\). The auxiliary linear deficit is zero. The exact decomposition \(\delta=P_B+C_B+\ell_B\) uses ordinary EPnI for the independent plus pair, **quantum conditional linear** qEPI for the minus pair, and information monotonicity/strong subadditivity for the loss. It does not use a conditional entropy-photon-number assertion. Internal entanglement within the original port remains arbitrary.

Here is the entire recovery chain underlying the original constant. Write \(\sigma_{CJ}=(\mathrm{id}\otimes\Phi_B)\omega\). Apply the flagged instrument on \(C\). On the erased branch of probability \(p>0\), let the normalized pre-erasure state be \(\widehat\sigma_{CJ}\). The information-loss chain gives \(pI(C:J)_{\widehat\sigma}\le\ell_B\). Its product reference is \(\widehat\sigma_C\otimes\widehat\sigma_J\), with the **filtered** \(J\) marginal. Quantum Pinsker yields the unnormalized error at most \(\sqrt{2p\ell_B}\le\sqrt{2\ell_B}\). Applying the inverse filter on \(P_L\) costs \(C_{y,L}\), not its square root. Because the inverse restores the \(C\) marginal exactly, the recovered product is the compressed original \(\sigma_C\) tensored with \(\widehat\sigma_J\).

The energy of \(C\) is \(te+(1-t)nr\le F=E+nr\). Gentle compression of \(\sigma_{CJ}\) costs at most \(2\sqrt{F/(L+1)}\); the corresponding product compression has the same bound, since its \(C\) marginal is the same. This first gives

\[
\|\sigma_{CJ}-\sigma_C\otimes\widehat\sigma_J\|_1
\le C_{y,L}\sqrt{2\ell_B}+4\sqrt{F/(L+1)}.
\]

Taking the \(C\) partial trace bounds the discrepancy between \(\widehat\sigma_J\) and \(\sigma_J\) by this same quantity. A second triangle inequality proves exactly

\[
\epsilon_B\le2C_{y,L}\sqrt{2\ell_B}+8\sqrt{F/(L+1)}.
\]

Finite positive branch probabilities and bounded filters preserve finite conditional energies; the prepared bath and all memories have finite energy and entropy for each finite \(y\). A uniform entropy bound as \(y\to\infty\) is neither needed nor claimed. The \(C\)-tail bound is independent of \(y\) because the auxiliary channel is on the other system. This verifies the full quantum bound, rather than just its scalar instrument coefficient.

### B3 — three cutoffs: PASS without repairs

The auxiliary noise exponent at the original Weyl test is

\[
A_y=\frac{2y+3/2}{4(1-t)}+
\frac{(r+1/2)(1-2t)^2}{4t(1-t)}.
\]

The signal argument remains \(z\), and the thermal cancellation gives the same dyadic relation as W120. Subdivision bounds the characteristic error on \(|z|\le Q\) by
\((B_0Q^2+2)e^{A_yQ^2}\sqrt{\epsilon_B}\), with \(B_0=2E+n+r+1/2\). Weyl Plancherel integrates its square with ball volume \(Q^{2n}/n!\). The inherited finite-energy Hilbert–Schmidt ladder-domain passage gives the separate frequency tail \(J/Q^2\), \(J=8(E+nr)+8n\). The Fock compression then costs rank \(\binom{K+n}{n}\) and the separate trace tail \(2(\sqrt E+\sqrt{nr})/\sqrt{K+1}\). These reproduce B3 exactly. The cutoff \(L\) of B2, the frequency radius \(Q\), and the number cutoff \(K\) have not been identified with one another. The original small-error restriction \(0<\epsilon_B\le e^{-4}\) is respected. No fourth moment, differentiability of a noisy functional equation, or inverse channel was inserted.

### B4 — optimization obstruction: PASS without repairs, restricted to this composition

The coefficient of \(\ell_B^{1/4}\) in the characteristic estimate has exponential factor
\(\exp\{A_yQ^2+(L/2)\log(1+1/(2y))\}\).
For \(y\ge1/2\), its exponent is at least

\[
\frac{yQ^2}{2(1-t)}+\frac{L}{8y}
\ge\frac{Q\sqrt L}{2\sqrt{1-t}}.
\]

The logarithm bound and AM–GM constants agree with the original. For \(0<y<1/2\), the second term is at least \((L/2)\log2\). Making the *displayed* filter tail and number tail polynomially small in a trace tolerance forces polynomially large \(L,K\); making \(\sqrt{\operatorname{rank}P_K}/Q\) small also forces a growing \(Q\). Thus optimizing this positive coefficient cannot produce a polynomial signal budget. The filter tail is additionally amplified upon insertion into B3. This is a cost obstruction in a particular derived upper bound. It is not a lower bound on the actual deficit, an admissible no-power sequence, or an impossibility theorem for all choices of tests or remainders.

### B5 — plus remainder and relative entropy: PASS without repairs

The actual entropy slice gives \(r_B=(r+B)/2\le x_B\le V_B=E/(2n)+B/2\). On this interval, \(-g''\ge1/[V_B(V_B+1)]\). Applying the independent-port EPnI and subtracting the linear baseline therefore gives

\[
P_B\ge\frac{nt(1-t)(x_B-r_B)^2}{2V_B(V_B+1)}.
\]

Integrating \(g'\le h(r_B)\) gives precisely B5 for \(z_B=n(g(x_B)-g(r_B))\). The attenuated energy is \((e+nB)/2\); substituting the thermal logarithm gives exactly

\[
D(\Phi_B\rho\Vert\tau_{r_B})=\tfrac12h(r_B)(e-nr)-z_B.
\]

Pinsker and \(z_B\ge0\) imply only the original unconditional bound
\(\|\Phi_B\rho-\tau_{r_B}\|_1\le\sqrt{h(r_B)(E-nr)}\).
It tends to zero as \(B\to\infty\) for every admissible input. There is no inference back to unsmoothed trace distance and no scalar replacement of \(C_B\) with quantum memory.

**Contribution gate, separate from correctness.** A1 is continuous scalar BV calculus applied to the accepted finite-energy EPnI and the inherited Stieltjes identity. The heavy tail is an exact-entropy domain obstruction, with a legitimate positive factorial-moment computation. B1–B5 quantify an existing erasure operation, inherited recovery and Fourier cutoffs, and a scalar optimization loss. They are useful technical statements, not a new stability mechanism. No new audit failure was found. Target B stays parked, unproved and unrefuted.

## 3. Overlap screen and precise candidates

AGENTS.md, upstream identity, current ledger entries, and the frozen TEN-FINDINGS history were checked. The long ledgers were frozen in full but are not represented as wholly semantically read. I26's original and resumed briefs and its complete resumed probability report were read. Its source comparison explicitly identifies the quenched monotone threshold law as already supplied by the Voronoi source; its frozen-geometry recoloring discussion reuses signed history and pivotal operations. The outstanding birth/death geometry, logarithmic Ising CLT, and integer-height field/curve questions remain their specific old gaps. None is renamed as a new I126 nomination. I07's complete parent probability screen concerns the four-state tree reconstruction and quantum-channel/conditional-EPnI probes. The pertinent I13 nonconventional mixing passage and I17 common-disorder SK passage were also read. The latter reinforces the need to identify a common coupling, but is a different model. No accepted finding identified in those passages is reproduced as a new result here.

The catalogue supplied leads only. The operation comparisons below use pinned manuscript statements and proofs, with exact local paths and reading ranges in the manifest. The selected inventory also retains the companion family paths; inventory inclusion does not mean semantic reading of every byte or importing every theorem.

The current history also led to a direct check of I72 §7 through its ending: its bounded-activity comparison uses extreme state weights and Dirichlet-form comparison for a weighted switch chain. E126 instead averages symmetric independent log-odds perturbations of an arbitrary finite law. That distinction does not elevate it above the technical contribution category shared by both comparisons.

### Candidate G1: FK-map diffusion, spectra, and finite-time occupation — reject as technical

For the critical FK-Ising rooted map pair \((M,A)\) with \(n\) edges, weight \(2^{\ell(M,A)/2}\), \(\ell=k(A)+k(A^*)-1\), use the **entire map**, including loops and parallel edges. Vertex mass is \(\deg(v)/(2n)\). A walk chooses a uniformly random incident half-edge, and time is accelerated by \(n\). The continuum is the unit-area \(\sqrt3\)-LQG sphere with Brownian generator associated with \(\frac12\int|\nabla f|^2\). Keep the source conformal embedding and its admissible deterministic metric scaling \(a_n\), not a new arbitrary metric normalization.

A seemingly substantial proposal is joint convergence of that full embedded metric-measure map, finitely many conditionally independent stationary walks, the spectrum, and \(T^{-1}\int_0^T\delta_{X_s}\,ds\) for fixed \(T>0\). The complete path proof already works pathwise on a common geometry extraction. Local energy recovery produces uniform cutoff functions; a forward/backward stationary martingale estimate controls their resolvent approximations along whole paths; stopping-time bounds prove tightness. The final proof pays the discrete attempt clock, the cable interpolation, and common compact metric gluing. Conditional kernels, finite products, and then averaging give the same-surface law. This is not merely separate marginal convergence.

The spectral companion's complete final section first matches the two physical corner orders, proves strong compactness using finite-rank energy approximations, then controls centered inverse kernels. Its tail bound has exponent \(p=7/10>1/2\), and its inverse limit and geometry live on that same extraction. The unhalved form operator is twice the Brownian generator; the final normalization is \(n\lambda_{n,j}\to\Lambda_j\). The heat-trace consequence is uniform on **fixed** \([\delta,T]\), \(0<\delta<T<\infty\), using eventual pathwise constants and a high-index tail. It is not an assertion uniform as time approaches zero, and provides no automatic annealed UI of those random constants.

Adding fixed-time occupation to these continuous-path conclusions is a bounded continuous integral mapping. Combining the pathwise operator and walk operations retains the joint surface law without an independent new coupling construction. The tree-weighted linear-clock companion likewise already pays conditional resolvent/FDD identification and the clock constant one. This candidate is rejected as technical. A shrinking-time heat trace, arbitrary deterministic starting vertex, or annealed inverse-gap moment statement would need extra estimates; none is nominated from the headline.

### Candidate G2: occupation under fixed weak FK-Ising disorder — selected, unresolved

The natural-occupation companion already proves the full pure square-lattice theorem for every fixed \(1\le q<4\): a **single deterministic constant** times \(n^{-d}\) times actual interface traversal count converges jointly with the ordered curve, including total mass. Its proof is not an exponent-transfer argument. The outward two-arm coupling retains the transmitted primal/dual regions and the distinguished interface under arbitrary permitted exterior reweighting. Electric correlations, the spectral estimates they use, and microscopic-to-disk calibration produce summable adjacent-scale errors and a positive amplitude along the full mesh sequence. Its final \(L^2\) comparison treats nearby pairs, separated pairs, boundary strips, and whole-plane tubular content. Merely proposing this pure theorem would duplicate an existing companion.

The weak-disorder companion proves a different theorem: fixed sufficiently small symmetric iid two-valued physical bond disorder, tuned to its physical critical point, has quenched **ordered-curve** limit SLE\(_{16/3}\) in environmental probability. Its exact local additions retain common partition-function scalar factors and the same projected disorder on different sheets. Its polygon proof runs to a fixed terminal physical scale; its moving-domain proof chooses deletions, punctures, a finite cover, and a fixed polygon before the mesh limit. Finally bounded martingale tests identify the driver and complete curve. These operations do not assert a relative microscopic two-arm amplitude or convergence of traversal count.

This leaves a genuine coupled normalization question, formulated in §4. It is different from I26's frozen Voronoi recoloring, its already-proved monotone thresholds, and its parked Ising/height questions. The thermal massive-SLE companion concerns deterministic thermal mass and its capacity drift, not this disordered critical counting measure; it supplies no normalization transfer used here.

### Candidate G3: exact-length honeycomb bridges with a specified endpoint — viable gap, not selected

Let \(p\) be the source critical irreducible strict-bridge probability law; a piece has visited-vertex length \(L\), height \(T\), horizontal displacement \(X\), and diameter \(\mathcal D\). The source spatial lattice is \(\Gamma=\{(h,m+h/2)\}\), with a specified full-rank difference sublattice and compatible piece counts. A precise strengthening would prove a uniform polynomial lower bound

\[
\sum_{k\ge1}p^{\otimes k}\{\textstyle\sum L_i=n,
\sum(T_i,X_i)=(h,x)\}\ge n^{-C_*}
\]

for every sufficiently large **compatible** target in a prescribed interior compact range \(c n^{3/4}\le h\le C n^{3/4}\), \(|x|\le C h\), with constants allowed to depend on that compact range. Compatibility would have to include the actual joint length/endpoint support, not just parity. Such a denominator would allow the source's absolute exceptional-mass bounds to be used under genuine local endpoint conditioning.

The source has two different complete operations: a spatial local lower bound of order \(H^{-5/4}\), summed over \(k\asymp H^{3/4}\), with **inequality** restrictions on total length and diameter; and a one-dimensional exact-length renewal bound, with terminal height and endpoint free. The former uses full spatial support of subsequential Lévy measures, Fourier decay on the difference lattice, and truncated mark control. The latter pays an exact-length denominator, then obtains geometric bounds by splitting the piece list rather than assuming within-piece independence. Its prescribed-target thermal result sums lengths with fugacity and uses a corridor denominator before tails. None conditions on exact length and endpoint simultaneously.

The all-length mass/covering companion gives the unrestricted uniform \(n\)-edge walk, free endpoint, diameter \(n^{3/4\pm\delta}\), and simultaneous mass/covering estimates with arbitrarily high polynomial probability. Its normalization lower bound cannot simply be reused for a rare exact endpoint. The full insertion proof in the renewal companion also pays representation multiplicities, sorted seams, rank versus original pairings, and thermal length mixing; it does not create the missing joint local denominator. This is a viable specific gap, but would require new joint \((L,T,X)\) lattice smoothing/support control. Neither separate local limit identifies it. It is not nominated, and the normalization question G2 provides the cleaner two-route investigation this round.

### Candidate G4: exact SLE gauge as a discrete length limit — reject the proposed inference

The explicit-gauge companion concerns ordinary chordal SLE\(_\kappa\), \(0<\kappa<8\), \(d=1+\kappa/8\), with
\(h(r)=r^d(\log\log(1/r))^{(2-d)/2}\)
near zero, and positive finite Hausdorff measure of every fixed positive-time segment, simultaneously as stated there. The earlier exact-gauge companion has a different construction; their relation is not automatically an equality of measures. Neither Hausdorff result proves that microscopic traversal count converges, nor identifies that count with Minkowski content. Normalization, tightness, boundary mass, and same-sample identification still have to be paid. G2 uses the actual pure occupation proof, not this gauge shortcut. The I124 distance/incidence and I125 Dini/free-boundary targets are excluded.

## 4. Exact selected target and source limits

Fix \(D=(0,1)^2\), \(a=(0,0)\), \(b=(1,1)\). Use the pure occupation source's finite graph on \(n^{-1}\mathbb Z^2\cap\overline D\): the top and left boundary arcs are wired together, their boundary edges omitted from the sampled edge set and treated as open for drawing; the bottom and right arcs are free, with their edges sampled. The remaining sampled set has \(M_n=2n^2\) edges. Use exactly its medial interface from \(a\) to \(b\), full medial-edge traversals, and projection \(\Pi\) clamping to \(\overline D\). Initial/terminal half-edges and artificial connectors carry no counting mass. A double visit to a vertex is not confused with the distinct full-edge traversals counted by the source.

Choose independent fair signs \(\xi_e\). For fixed \(0<\varepsilon<\varepsilon_0\), let physical Ising couplings be \(J_e=1+\varepsilon\xi_e\), at the source's physical critical inverse temperature \(\beta_c(\varepsilon)\). The pinned critical-point input, not an independent inference from self-duality, gives exactly

\[
v_e=e^{2\beta_c(\varepsilon)J_e}-1
=\sqrt2e^{\theta(\varepsilon)\xi_e},\qquad \theta(\varepsilon)>0.
\]

The quenched FK law is normalized **separately for each environment**:

\[
\phi_{n,\xi}(w)=Z_{n,\xi}^{-1}
2^{k(w)}\prod_{e\in E_n}v_e^{w_e}.
\]

Environment expectation always means the original independent-sign probability. It is not reweighted by \(Z_{n,\xi}\).

Let \(\gamma_n\) be the ordered interface modulo increasing reparametrization. The target asks whether for each fixed such \(\varepsilon\) there is one deterministic \(0<c_\varepsilon<\infty\), independent of \(n\), such that

\[
\mathcal L_{\phi_{n,\xi}}\left(
[\gamma_n],\ c_\varepsilon n^{-5/3}
\sum_{e\text{ traversed}}\delta_{\Pi(z_e)}\right)
\ \longrightarrow\ \mathcal L(\gamma,\mu_\gamma)
\tag{G}
\]

in probability over environments, in bounded-Lipschitz distance on the product of bounded ordered-curve metric and weak topology of positive finite measures on \(\overline D\). Here \(\gamma\) is chordal SLE\(_{16/3}\) in this square from \(a\) to \(b\), and **on that same sample**

\[
T_r(\gamma)=r^{-1/3}\Pi_*
\bigl({\bf1}_{\{\operatorname{dist}(z,\operatorname{tr}\gamma)<r\}}dA(z)\bigr)
\ \longrightarrow\ \mu_\gamma
\]

in probability as \(r\downarrow0\), with the whole-plane tubular convention of the pure occupation source. Total mass is part of the asserted weak finite-measure topology. The statement does not assert convergence of unbounded moments, a rate, quenched almost-sure convergence along all meshes, or uniformity over arbitrary random domains. No capacity-to-natural-time substitution is made.

For fixed disorder the available local root-moment error is bounded in the source by \(A\sqrt{v_k}\), with \(v_k\le(v_0^{-1}+ck)^{-1}\). Its polygon construction needs decay, not summability, and only boundedly many terminal potentials at a fixed macroscopic scale. This is not a summable bound for a microscopic amplitude product. The pure calibration proof instead compares adjacent scales by a summable relative error. A vanishing macroscopic error alone leaves open a slowly varying amplitude. This is a limitation of the available estimate, not a construction of such an amplitude in FK-Ising and not a refutation of (G).

## 5. Route one: a necessary and sufficient annealed replacement criterion

This route keeps the fixed disorder and attacks the actual occupation measure. It pays the quenched/joint-law step completely and isolates exactly what the microscopic comparison must deliver.

Let \(\mathcal C\) be the ordered-curve space just specified, with its metric capped at one. Choose a countable uniformly dense subset \((f_j)\) of the unit ball of real \(C(\overline D)\), with \(f_1=1\), and use

\[
d_m(\lambda,\lambda')=\sum_{j\ge1}2^{-j}
\bigl(1\wedge|\lambda(f_j)-\lambda'(f_j)|\bigr).
\]

This metric gives weak convergence of positive finite measures. Indeed convergence for \(f_1\) bounds masses, after which uniform approximation gives convergence for every continuous test; the converse follows from dominated summation. Use sum product metric and the bounded-Lipschitz distance with tests bounded by one and Lipschitz constant at most one.

For a candidate constant \(c>0\), let \(\nu_n^c\) be the actual counting measure in (G). Define the **fully normalized** annealed discrepancy

\[
R_{n,r}(c)=\mathbb E_\xi\,phi_{n,\xi}
\bigl[d_m(\nu_n^c,T_r(\gamma_n))\bigr].
\]

**Proposition R126.** Assuming the stipulated fixed-disorder quenched curve theorem, (G) with constant \(c\) holds if and only if

\[
\lim_{r\downarrow0}\limsup_{n\to\infty}R_{n,r}(c)=0.
\tag{R}
\]

Moreover, for every \(a>0\), write \(K_{n,\xi}\) for the actual joint law, \(P_{n,\xi}\) for its curve marginal, \(Q\) for SLE law, \(F_r(\gamma)=(\gamma,T_r\gamma)\), and \(Q_*=\mathcal L(\gamma,\mu_\gamma)\). Then

\[
\begin{split}
\mathbb P_\xi\{d_{BL}(K_{n,\xi},Q_*)>3a\}
\le{}&R_{n,r}(c)/a\\
&+\mathbb P_\xi\{d_{BL}((F_r)_*P_{n,\xi},(F_r)_*Q)>a\}\\
&+{\bf1}_{\{d_{BL}((F_r)_*Q,Q_*)>a\}}.
\end{split}\tag{R1}
\]

**Proof.** For fixed \(r>0\), ordered-curve convergence implies Hausdorff convergence of traces and hence uniform convergence of their distance functions. A positive level set of distance to a compact planar set has area zero: at a differentiability and density point of such a level set, its gradient would be zero, whereas the distance function is differentiable with gradient norm one almost everywhere off the compact set. All tubes lie in a common bounded enlargement of the square. Dominated convergence therefore proves \(T_r(\gamma_k)\to T_r(\gamma)\) weakly. This also proves measurability and continuity of \(F_r\).

Couple the two pairs \((\gamma_n,\nu_n^c)\) and \((\gamma_n,T_r\gamma_n)\) using the **same configuration**. Every allowed BL test changes by at most \(d_m(\nu_n^c,T_r\gamma_n)\). Thus their quenched-law distance is bounded by the corresponding quenched expectation. Markov's inequality over environments gives the first term of (R1). The triangle inequality proves the display. For fixed \(r\), the second term tends to zero by the quenched curve theorem and continuity of the pushforward on probability laws. Equivalently, apply the deterministic subsequence criterion for convergence in probability before the usual continuous mapping theorem. The third term vanishes for all sufficiently small \(r\), because the SLE tubular measures converge in probability on the same SLE sample. Under (R), first choose \(r\) and then let \(n\to\infty\); (R1) proves the sufficiency.

Conversely suppose (G) holds. For fixed \(r\), the function
\((\gamma,\lambda)\mapsto d_m(\lambda,T_r\gamma)\)
is bounded and continuous. Quenched weak convergence in probability implies convergence of its conditional expectations in probability, and boundedness then implies convergence of their environment averages. Therefore
\(R_{n,r}(c)\to\mathbb E,d_m(\mu_\gamma,T_r\gamma)\).
This last expression tends to zero as \(r\downarrow0\), by bounded convergence in probability. This proves necessity. ∎

This gives a quantitative route from an annealed estimate to a quenched **joint** result without assuming two independent marks have the correct conditional dependence. The curve already determines its limiting mark; the same-configuration replacement is what enforces that dependence. No additional environmental variance estimate is needed once (R) is paid.

A useful testwise sufficient estimate follows directly. Let \(\chi_\delta\in C(\overline D)\) equal one outside a boundary strip of width \(2\delta\), and zero in the strip of width \(\delta\). Put

\[
A_{n,r,\delta,j}=
\left[\mathbb E_\xi\phi_{n,\xi}
|\nu_n^c(\chi_\delta f_j)-T_r\gamma_n(\chi_\delta f_j)|^2\right]^{1/2},
\]
\[
B_{n,r,\delta}=
\mathbb E_\xi\phi_{n,\xi}
[(\nu_n^c+T_r\gamma_n)(1-\chi_\delta)].
\]

For every finite \(J\), positivity, the triangle inequality, and Cauchy–Schwarz give the **paid** bound

\[
R_{n,r}(c)\le2^{-J}+\sum_{j=1}^J2^{-j}A_{n,r,\delta,j}
+B_{n,r,\delta}.\tag{R2}
\]

Thus uniform interior \(L^2\) replacement and vanishing boundary first moment in the order \(n\to\infty\), then \(r\downarrow0\), then \(\delta\downarrow0\), with \(J\to\infty\) last, suffice. Tightness is also paid by this argument: the total-mass test is included, positive measures of bounded mass on the compact square form a compact set, and curve tightness is already available. It does not demand a false global second moment at a rough boundary.

For the pure law, the source proves exactly this type of estimate: near-diagonal summation and separated two-arm coupling, plus boundary first-moment control, followed by its nonzero microscopic calibration. Under fixed disorder these are not established by the polygon/slit comparison. Its deletion errors concern bounded crossing tests with geometric radii fixed before the mesh; dividing such errors by microscopic two-arm probabilities is unjustified. Conditioning on a hit changes the environment's posterior law, so iid signs cannot be reused inside that conditioning without a proof. Repeated sheets retain the same physical bonds. These observations prevent a silent import of the pure outward-coupling minorization or its reference amplitude.

**Route-one status.** R126 and R1–R2 are proved technical criteria, not (G). The exact remaining obligation is existence of a deterministic finite positive \(c_\varepsilon\) satisfying (R). R2 decomposes it into concrete local comparison and boundary budgets; it does not claim those budgets for the disordered model. In particular this report proves neither their summability nor an obstruction in an actual fixed-disorder FK sequence.

## 6. Route two: exact entropy control of normalized random tilts

This second route bypasses local interface geometry by controlling the entire finite-configuration law. It closes a genuine, narrower regime, while exposing precisely why it stops for fixed disorder.

**Proposition E126.** Let \(P_0\) be any probability law on a subset of \(\{0,1\}^M\), with arbitrary dependence. For \(s\in\mathbb R^M\), set

\[
A(s)=\log E_0 e^{\sum_i s_iX_i},\qquad
P_s(x)=e^{s\cdot x-A(s)}P_0(x).
\]

Let \(s_i=a_i\xi_i\), where the signs are independent and fair and the deterministic amplitudes \(a_i\ge0\) are finite. Then

\[
\mathbb E_\xi D(P_s\Vert P_0)\le\tfrac14\sum_i a_i^2,
\quad
\mathbb E_\xi\|P_s-P_0\|_{TV}^2\le\tfrac18\sum_i a_i^2.
\tag{E1}
\]

Here TV is the usual *half* of the classical \(\ell^1\) distance. Consequently

\[
\mathbb E_\xi\|P_s-P_0\|_{TV}\le\sqrt{\sum_i a_i^2/8},
\qquad
\mathbb P_\xi\{\|P_s-P_0\|_{TV}>u\}
\le\frac{\sum_i a_i^2}{8u^2}.
\tag{E2}
\]

All these estimates contract under any deterministic measurable readout, including a whole curve together with its actual finite counting measure. The constants are independent of the graph, its correlations, its boundary partition, and the readout.

**Proof.** The state space is finite, so all derivatives and exchanges below are ordinary finite sums. The exact centered score is \(X_i-E_sX_i\), giving
\(\partial_iA=E_sX_i\), \(\partial_i^2A=\operatorname{Var}_sX_i\le1/4\).
The relative entropy is
\(D(P_s\Vert P_0)=\sum_i s_i\partial_iA(s)-A(s)\).
Convexity of \(A\), mean-zero \(s\), and \(A(0)=0\) give \(\mathbb E A(s)\ge0\). Holding the other signs fixed,

\[
\mathbb E_{\xi_i}[a_i\xi_i\partial_iA(s)]
=\frac{a_i}{2}\{\partial_iA(s_{-i},a_i)-\partial_iA(s_{-i},-a_i)\}
=\frac{a_i}{2}\int_{-a_i}^{a_i}\partial_i^2A(s_{-i},t)dt
\le a_i^2/4.
\]

Sum over \(i\), then subtract the nonnegative average \(A\). This proves the entropy estimate without any independence of the \(X_i\). For completeness Pinsker in this convention follows by grouping configurations into the positive and negative parts of \(P_s-P_0\) (log-sum inequality), then using the Bernoulli relative entropy lower bound \(d(p\Vert q)\ge2(p-q)^2\), obtained by integrating its second derivative in \(p\), \(1/[p(1-p)]\ge4\), from the minimum at \(p=q\). Hence TV squared is at most half the relative entropy. Cauchy–Schwarz, Markov, and contraction under measurable maps prove the rest. ∎

There is also a deterministic-centering extension useful for checking parameter conventions. If \(s_i=b_i+a_i\xi_i\), compare first to \(P_b\). The proof of E1 applies with \(P_b\) as reference. Between \(P_b\) and \(P_0\), integration along \(tb\) and \(\operatorname{Var}(b\cdot X)\le(\sum_i|b_i|)^2/4\) give

\[
D(P_b\Vert P_0)
=\int_0^1 t\,\operatorname{Var}_{tb}(b\cdot X)dt
\le\tfrac18(\sum_i|b_i|)^2.
\]

Thus
\(\mathbb E TV(P_s,P_0)\le\sqrt{\sum_i a_i^2/8}+\frac14\sum_i|b_i|\).
This additional bound is proved here to make explicit why an uncontrolled deterministic shift cannot be called centered disorder. It is not used to replace the physical critical point.

**Application to the actual square model.** Take \(P_0=\phi_{n,0}\), the pure critical q=2 FK law with the same wired/free graph and sampled edges. The factors \(2^{k(w)}(\sqrt2)^{|w|}\) are contained in \(P_0\), so the Radon–Nikodym density of the physical critical quenched law is **exactly** the exponential tilt above with \(a_i=\theta(\varepsilon)\), \(b_i=0\). Since \(M_n=2n^2\),

\[
\mathbb E_\xi TV(\phi_{n,\xi},\phi_{n,0})^2
\le n^2\theta(\varepsilon)^2/4,\qquad
\mathbb E_\xi TV\le n\theta(\varepsilon)/2.
\tag{E3}
\]

Now let \(\varepsilon_n\) be a deterministic sequence in the source's admissible small-disorder interval, with \(n\theta(\varepsilon_n)\to0\), and tune each graph to its actual \(\beta_c(\varepsilon_n)\). Retain exactly the **pure** calibration constant \(c_0=c(2)\). Apply E3 to the deterministic readout
\(w\mapsto([\gamma_n(w)],c_0n^{-5/3}\sum\delta_{\Pi z_e})\).
Its quenched joint law differs in TV from the pure joint law by a quantity tending to zero in environmental probability. The stipulated full pure occupation theorem therefore proves (G) in this shrinking-disorder regime, including total mass. This is an actual discrete-to-continuum theorem for these parameters, not a lemma whose premise remains unpaid. It does not require separately establishing a disordered one-point Green function.

The convenient sufficient condition \(n\varepsilon_n\to0\) implies the stated condition. To see this with an explicit constant, put \(K_0=\frac12\log(1+\sqrt2)\). The exact critical odds relation implies \(K_-\le K_0\le K_+\), where \(K_\pm=\beta_c(\varepsilon)(1\pm\varepsilon)\). For \(\varepsilon\le1/2\), it follows that \(\beta_c\le2K_0\) and \(K_-\ge K_0/3\). The derivative of \(F(K)=\log(e^{2K}-1)\) is \(2/(1-e^{-2K})\). Therefore

\[
\theta(\varepsilon)=\tfrac12(F(K_+)-F(K_-))
\le\frac{4K_0}{1-e^{-2K_0/3}}\,\varepsilon.
\]

The entropy proof averages normalized quenched measures under the original fair signs. It does not replace them by a partition-function-weighted annealed law. The score is centered under the current tilted law; mean-zero log odds are not confused with mean-zero edge probability or mean-zero Ising coupling perturbation.

**Uniform integrability and conditioning limits.** Weak convergence of finite measures includes the total-mass distribution, not convergence of its expectation. A deterministic counting bound is \(\nu_n^{c_0}(\overline D)\le Cc_0n^{1/3}\), with a lattice constant independent of the configuration. Thus the TV estimate alone bounds the difference of expectations of total mass by \(C'c_0\theta_n n^{4/3}\); the same applies to bounded spatial tests times mass. This tends to zero only under the stronger displayed rate, unless another UI argument is supplied. Under \(\theta_n n^{4/3}\to0\), pure-source interior \(L^2\) control and vanishing boundary first moments imply annealed UI of total mass, which transfers by applying that deterministic bound also to mass tails. No higher-moment or fixed-disorder UI is claimed.

For a fixed deterministic graph/boundary partition E1 is uniform. After a random exploration history, the conditional environment can be biased and dependent, so the fair-sign proof cannot simply be restarted. Likewise conditioning on an event of probability \(p\) can amplify TV errors by a multiple of \(1/p\). This route gives no uniform rare-hit, exact-endpoint, or arbitrary random-domain conditional comparison. This is why it does not resolve the local obligation in route one.

For fixed positive \(\varepsilon\), E3 grows like \(n^2\theta(\varepsilon)^2\) and eventually gives no improvement over the trivial bound one. That is a limitation of this whole-configuration comparison, not evidence that (G) is false. No constraint-respecting fixed-disorder counterexample has been constructed.

## 7. Primary literature and operation-level contribution assessment

The pinned source paths are versioned by the accepted commit, not by a moving branch. The manifest records actual splitlines ranges and endings. Relevant completed operations read include Li's different-pair decomposition and flagged recovery through its proof and finite-energy appendix; the map path and tightness proofs and the spectral companion's entire final operator-to-spectrum section; the honeycomb exact-length argument, spatial-local argument and complete insertion/thermal proof; and the pure FK coupling, calibration, and occupation proofs, together with the disordered polygon, slit, and final driving/curve proofs. Lower source inputs are used at their stated scopes; catalogue entries and inventories are not themselves premises. The evidence records distinguish these complete operations from introductory/theorem-only reads and from acquired but unused text.

Direct pinned proof locations include the [pure occupation proof](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Natural-Occupation-Measures-for-Critical-Square-Lattice-FK-Interfaces-October-5-2026/build/sections/08-occupation.tex), its [outward coupling](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Natural-Occupation-Measures-for-Critical-Square-Lattice-FK-Interfaces-October-5-2026/build/sections/06-coupling.tex), the [disordered polygon comparison](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quenched-SLE-Universality-for-Weakly-Disordered-FK-Ising-Interfaces-October-5-2026/build/sections/polygon.tex), its [slit-domain proof](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quenched-SLE-Universality-for-Weakly-Disordered-FK-Ising-Interfaces-October-5-2026/build/sections/slits.tex), and the [joint spectral proof](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Spectral-convergence-for-critical-FK-Ising-planar-maps-October-5-2026/build/tex/09-spectrum.tex). The read manifest supplies the corresponding immutable local bytes and inclusive ranges, rather than relying on online rendering for replay.

Fresh primary-source retrievals fixed the following external versions. None is needed as an independently assumed theorem in the new proofs, whose non-elementary model inputs are pinned.

* **Holden–Li–Sun, [1804.07286v3](https://arxiv.org/html/1804.07286v3)**, submitted March 29, 2021: the percolation interface normalization uses \(\eta^2/\alpha_2^\eta(\eta,1)\). Its complete measure-identification operation in §3 uses interior \(L^2\) replacement, arm estimates, and coupling of conditional local pictures, including the non-Jordan-domain issue. It already identifies the same-sample Minkowski mark; this is not a new conceptual contribution of R126. It treats triangular site percolation/SLE6, not the fixed-disorder square q=2 amplitude. Its discussion also separates measure convergence from parametrized-curve convergence in the presence of double points. We claim only the pair topology in (G).
* **Avérous–Mahfouf, [2509.08938v1](https://arxiv.org/html/2509.08938v1)**, September 10, 2025: the statements distinguish naive centering from a second-order natural centering of random bond probabilities and give quenched RSW stability in enhanced shrinking windows. The read differential proof in Appendix A.1 differentiates the **normalized** measure and produces covariances/cumulants. Its stochastic interpolation uses stopped Brownian perturbations and arm/mixing-rate estimates. The current entropy proof uses a cruder whole-configuration comparison, with a much smaller window, and elementary one-coordinate curvature. It is not an improvement of those geometric windows, nor a fixed-disorder natural-time result. External displayed formulas are not used as algebraic premises: E126 derives its own score and constants.
* **Lawler–Rezaei, [1211.4146v2](https://arxiv.org/html/1211.4146v2)**, June 19, 2015: the theorem read identifies SLE Minkowski content and its natural clock, with Green-function moments in its stated domains. Here the full square/boundary tubular operation is supplied by the pinned occupation proof; no general rough-domain extension is imported from this external theorem statement.
* **Berestycki–Gwynne, [2003.10320v2](https://arxiv.org/html/2003.10320v2)**, July 29, 2022, was acquired as a map-diffusion literature lead. Its acquisition is not claimed as a complete proof reading or as an input for the rejected G1 screen. The decisive duplicate comparison there is to the complete relevant pinned map operations, including their same-surface conditional identification.

These searches and comparisons are not exhaustive worldwide priority evidence. In particular, the elementary random-tilt entropy inequality may have equivalent formulations elsewhere. Its proof here is independent and fully stated; its contribution is a quantitative technical transfer. R126 is a standard replacement principle made precise for quenched marked laws and the actual source normalization. Neither partial qualifies for a substantial nomination on this evidence. The selected fixed-disorder problem remains open in this report.

## 8. Evidence and validation

The owned inventory consists exactly of this report and the two I126 roots authorized in the brief. `references.json` binds original task/report/parent receipt, the required recursive record, instructions, identity, and the history snapshots. Only the four live ledgers may drift; their frozen snapshots cannot. No I124/I125 working output is bound. Historical names in immutable task records or frozen ledgers do not make those active outputs dependencies.

The 10,373-position original mapping is reused in place. The offline verifier invokes the already sealed I123 **flat engine once**; that engine verifies the I114/I117/I120 packages, all mapped original bytes and Git blobs, the 776 existing PDF-view bindings, inherited exact lexical occurrence multisets, inventories, and HTML/provenance conventions without calling nested corpus verifiers. I126 first validates all its additional immutable bytes, snapshots, read records, exact selected lexical multisets, selected inventory, and deterministic HTML views. Only after those checks and the inherited engine's immutable checks may finite diagnostics run. No corpus tree or nested package tree is copied.

Read records preserve UTF-8 splitlines ranges, LF counts, endings, decoded JSON-field conventions, and range hashes. Exact lexical occurrence multisets are mechanical evidence, not proof of semantic coverage. The failure log retains output truncations and their recovery or limited-read disposition. Fresh external HTML and metadata retain response provenance and versions. No PDF was re-extracted. The verifier is offline and read-only, disables bytecode, and blocks network, writes, subprocesses, repairs, and resealing. Acquisition/read-ledger scripts are separate and are never run by it.

Run from the research directory:

```bash
python3 -B frontier/experiments/i126_random_geometry_discovery/verify.py
```

Preseal validation is performed before the single final seal. The finite diagnostics check rational one-coordinate tilt/normalization identities, exact score centering, Bernoulli variance bounds, conditional-reference distinctions, and coefficient arithmetic, alongside the unchanged inherited diagnostics. They do not certify any universal proof, novelty, rate for fixed disorder, or substantiality.

**Disposition for the parent:** retain the original I123 no-repair passes, preserve all inherited scopes, and keep thermal Target B parked. Record R126 and E126, including the actual shrinking-disorder joint occupation limit, as technical paid partials. Do not nominate (G), the SAW local-conditioning gap, or a routine map/gauge corollary. The minimal remaining fixed-disorder obligation is a deterministic positive calibration satisfying the exact replacement condition (R); neither route has paid it.
