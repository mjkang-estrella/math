# S236 — independent adversarial correctness review, round 1

**Recommendation to the parent: PASS for the entire unchanged frozen statement and submitted proof, relative to the stipulated upstream truth.** This is a proposed correctness disposition only. The parent alone adopts a verdict. I assign no contribution verdict, acceptance, or count.

The reviewed statement is the 4,312-byte `STATEMENT.md`, SHA256 `ad83c8bcf032a77734228b59ef8e4721215d0c09907e9e504a7df934ab89af1e`; the submitted proof is the 31,149-byte `AUTHOR-PROOF.md`, SHA256 `c8b6f21d138c4ce517e073dc45bf445c49bb1d21dc1c404f1cedef478cc97cb5`. I also read all of COMPARISON, prefreeze-derivations, orientation, FINAL, and the outside REPORT. The conclusion below concerns their auxiliary mathematical scope claims as well as S1–S5. It does not certify a replacement theorem.

I found no essential mathematical repair, extra hypothesis, narrowing, replacement, or remaining verification obligation needed to obtain S236. Several compressed steps require unpacking; the calculations below identify why they are consequences of the displayed equations and the actual cited source interfaces. My access and comparison limits are recorded separately in `READING-LIMITS.md`. In particular, hashing is not proof reading, primary comparisons are not premises, and the older H proof has not been regraded. The supplementary `derivations.md` records the main calculations in more algebraic detail.

## 1. Exact scope and actual source interfaces

S236 fixes \(m=2s-1\), \(s\ge4\), \(0<a_*<1<q_*\), with the **whole-interval strict inequality S1**. It allows every prescribed finite cyclic partition of each real \(V_l\), simultaneously for all \(l\ge2\), without uniform bounds in degree. The conclusion is one metric, its entire pointwise growth filtration at every real \(d\ge0\), exact logarithmic exponents, included critical endpoints with the specified negative correction, and the geometric and explicit nonvacuity assertions. Neither an integer-only count nor a finite collection of blocks would meet this scope.

S1 is consistent: for any fixed \(m\ge7\) and \(a_*<1\), continuity at \(q=1\), where its right side is 1, permits some \(q_*>1\). The specified numerical example is checked in section 11. S1 also forces the horizontal Ricci factor to remain positive; the proof never independently varies \(q_*\) beyond that restriction.

Source A's headline is an existence assertion for some even dimension n>=8 and integer k>=2. Source B's headline covers every 4/9<v<1 and 1<c<9v/4, for all sufficiently large integers k, with a metric allowed to depend on k. Its near-Euclidean flexibility is at each fixed 1<c<9/4 with the stated parameter choices; it is not a single-metric all-k conclusion. I read Source A's actual algebra and transmission, not just its existence theorem. Its link calculation gives, on every round harmonic degree and for every orthogonal complex structure \(J\),

\[
 A_l=a^{-2}q^{1/m}\{B_lI+(q^{-1}-1)(-D_J^2)\},\qquad B_l=l(l+m-1),
\]

with exact invariance of \(V_l\) and angular volume \(a^m d\mathrm{vol}_0\). Its complex bidegree dimensions are

\[
 h_{l,b}=\binom{s+b-1}{s-1}\binom{s+l-b-1}{s-1}
 -\binom{s+b-2}{s-1}\binom{s+l-b-2}{s-1},
\]

with the usual zero-binomial convention. The charge is \(2b-l\). Conjugate components combine into real dimension \(2h_{l,b}\) when distinct; the self-conjugate component has real dimension \(h_{l,b}\). Summing over all b already supplies the correct real dimension \(N_l\); no additional doubling is allowed. This is exactly S2's convention and covers every degree.

Source A's finite algebraic interface is the direct sum of \(\mathfrak{sl}(V_l)\), \(2\le l\le L\), for \(s\ge4\), with the positive degree-dependent generator coefficients already included. Both orientations and signed areas occur in its argument; retaining only one orientation would not be an interchangeable interface. Proposition `prop:word` supplies a finite smooth word and a parameter slice with nonsingular derivative **at any prescribed product-SL target**, not merely near the identity or in one block. Its transmission supplies center-regular graphs, uniform-past resets, the exact scalar baseline and C1 estimates, and removal of the whole following diagonal leg. The slower-tail bounds themselves are checked below, rather than imported at the source's original rate.

Source B was also read through its actual stronger operative mechanisms. These include isolated adjacent doubles and finite larger-cutoff avoidance; fixed-area angular programs; whole-ball inward operators preserving constants and mean and contracting L2; an infinite high-mode graph above a protected **fixed finite rank**; the distinction between full-operator o(1) freezing and the sharper finite-frame error \(O(\eta\log(1/\eta)+\eta^2)\); signed divided-difference crossing coefficients; one scalar obstruction per double with the reversed ordered pair's zero/matching roles exchanged; Gaussian stable weights; countably many simultaneous matches; compatible whole-ball traces; and every-radius pointwise estimates. Its near-Euclidean flexibility and geometric conclusions remain paid source operations. None provides an unstated inverse estimate uniform as rank tends to infinity. S236 does not need such an estimate or import B's future-dependent graph as a center-regular graph. Its new deduction here uses A's exact finite-dimensional invariant blocks. Source truths are stipulated; I have not audited or challenged them.

## 2. Smooth radial prefix, cutoff, and admissible signed pulses

The explicit piecewise interpretation in AUTHOR-PROOF lines 51–76 is necessary and sufficient: \(b=0\) for \(t\le B\), and the fractional-power formula is used only for \(t>B\), with \(B>0\). Thus there is no evaluation of \((1+t)^{-17/16}\) at negative base. Flatness of a smooth cutoff constant on the preceding half-line gives smooth gluing. The integral definition sets \(a=1\) there and makes \(a\) decrease to precisely \(a_*\), since \(\mu I_B=-\log a_*\).

For \(\delta=1/16\), \(I_B\asymp B^{-\delta}\), so \(\|b\|_\infty=O((-\log a_*)/B)\). Any allowed \(a_*\), not only one close to 1, is handled by increasing B. Direct differentiation gives the displayed identity

\[
 b+b'+b^2=-\mu\chi_B f\bigl[1-(1+\delta)/(1+t)-\mu\chi_B f\bigr]-\mu\chi_B'f\le0.
\]

The bracket is positive for large B and \(\chi_B'\ge0\). Consequently \(b\ge-1/4\), \(p=m-1+mb\ge3m/4-1>0\), and, past \(2B\), the negative of this expression is comparable to \(\mu(1+t)^{-17/16}\). Integrating the remaining tail gives exactly

\[
 \log(a/a_*)=(\mu/\delta)(1+t)^{-1/16}.
\]

The proof first chooses \(\bar a>a_*\) with strict S1 margin, then extends that margin by continuity to \(q\in[1-\epsilon_0,q_*]\), taking \(\epsilon_0<1\). This includes negative-area weak pulses, for which \(q<1\), without losing positive definiteness or link curvature. All early periods are round until \(a\le\bar a\) and the finite thresholds hold. Since the absolute schedule starts at \(t_1=10\), with q round throughout the preceding region, the first active period has an actual round predecessor; no reset is assumed before a round interval exists. The first activation can be placed after \(2B\). The core \(r\le e^B\) is exactly Euclidean, not a singular cone subsequently asserted to be smoothed. Completeness and volume are verified directly in section 7.

## 3. All-degree center-regular graphs and the exceptional degrees

Compact positive a,q ranges and \(0\le-D_J^2\le l^2 I\) imply

\[
 \kappa l(l+m-1)I\le A_l\le K l(l+m-1)I
\]

with \(\kappa,K\) independent of l, the selected word, and its length. For the symmetric Riccati equation \(P'=A_l-pP-P^2\), the proof's barrier test is valid for noncommuting matrices: at a first contact eigenvector with eigenvalue cl or Cl, \(P^2\) acts on that vector by \(c^2l^2\) or \(C^2l^2\). It is not necessary that A and P commute. The displayed small-c inequalities make the lower derivative strictly positive. \(C^2>Km\) suffices above since \(l(l+m-1)\le ml^2\). Core data \(P=lI\) lie inside these barriers.

Uniqueness preserves symmetry, and the barriers preclude finite-time blow-up. Solving \(Y'=PY\) from the core yields an everywhere invertible value fundamental matrix, with determinant equal to its initial positive determinant times \(\exp\int\mathrm{tr}P\). The Riccati equation then gives the original second-order equation. This establishes all regular solutions and their independence, rather than presupposing value-map invertibility to continue the Riccati graph. The resulting norm inequalities are

\[
 e^{cl(t-s)}\|Y(s)\|\le\|Y(t)\|\le e^{Cl(t-s)}\|Y(s)\|.
\]

For reset, write \(E=P-\theta_lI\) on the final round rest. Exactly,

\[
 E'=fI-(pI+P)E-E\theta_l,quad
 f=a^{-2}B_l-p\theta_l-\theta_l^2=O_l(j^{-1/2}).
\]

The damping is positive and uniform in the past, while the initial E is bounded by the all-degree barriers. A rest of length \((j-1)^6\) therefore gives \(E(t_j)=O_l(j^{-1/2})\), including degrees which have never been activated. Here \(t\asymp j^8\) throughout the rest. The first active period is covered by the round prefix just discussed. No constant uniform in l is claimed for this sharper reset.

For \(l=0\), the only center-regular radial solution is the constant; the other core solution is singular. For \(l=1\), \(-D_J^2=I\) for all J, so the entire equation is scalar on the \(m+1\)-dimensional real space. Neither an exceptional Lie-algebra assertion nor a missing control direction is needed. Its scalar transfer and endpoint estimates are addressed explicitly below.

## 4. Modified-tail residual, parameter differentiation, and uniformity in the past

Fix one finite level and hold its incoming graph fixed while varying the current parameter h. Put \(p_0=m-1\), \(\theta^2+p_0\theta=a_*^{-2}B_l\), \(T=j^6\), and \(\eta=j^{-1/2}+T^{-1}\). The baseline in the cited Source A construction has \(v(t_j)=\theta\) and solves \(v'=a^{-2}B_l-pv-v^2\). This initial datum is part of the expressly invoked baseline definition, not a new chosen boundary condition. Damping gives \(v-\theta=O_l(\eta)\).

In the source's notation, expressed as X here,

\[
 X(\tau,h)=\frac{a_*^{-2}}{p_0+2\theta}\sum_\beta c_\beta(h)\beta(\tau)
               (B_l I/m+D_{J_\beta}^2).
\]

It is trace free. Indeed the addition tensor \(\sum_a de_a\otimes de_a\) is the constant multiple \(B_lN_l/(m\operatorname{Vol}S^m)\) of the round metric; integrating its evaluation on the unit Hopf field gives \(\operatorname{tr}D_J^2=-B_lN_l/m\). This verifies the author's trace-free description without discarding a scalar term.

Taylor expansion of the exact angular operator, with one h derivative, gives

\[
 A_l=a^{-2}B_l I+(p_0+2\theta)X/T+E_A,
 \qquad \|E_A\|_{C^1_h}\le C_N(j^{-1/2}/T+T^{-2}).
\]

For \(Q=vI+X/T\), the **exact** residual is

\[
 \rho=A_l-pQ-Q^2-Q'
 =E_A-[(p-p_0)+2(v-\theta)]X/T-(X^2+X_\tau)/T^2.
\]

Thus \(\|\rho\|_{C^1_h}\le C_N\eta/T\). If \(E=P-Q\), then exactly, with the indicated factor order,

\[
 E'=\rho-(pI+P)E-EQ.
\]

P is positive by section 3, Q is uniformly positive for large j at this finite level, and p is positive. Two-sided matrix damping, for example in the Frobenius norm as in Source A, gives

\[
 \sup\|E\|\le C_N\eta,\qquad \int_{\rm control}\|E\|\,dt\le C_N\eta.
\]

The initial error is \(O_l(\eta)\); it decays on a bounded time scale. Its current-parameter derivative is zero because earlier periods and v's initial value are fixed and the pulse vanishes near its initial endpoint. With \(Q_h=X_h/T\), exact differentiation yields

\[
 E_h'=\rho_h-(pI+P)E_h-E_hP-Q_hE-EQ_h.
\]

Its forcing is \(O(C_N\eta/T)\), and its integral is \(O(C_N\eta)\). Damping consequently gives the same integrated bound for \(E_h\). This explicitly supplies the claimed parameter estimate, including the incoming graph, rather than differentiating an unproved big-O assertion.

The normalized value map \(F=e^{-\int v}B\) satisfies \(F'=(X/T+E)F\). The integrated bounds, and their differentiated equations on the fixed compact parameter ball, give C1 convergence to the ideal finite word. In particular **\(T\eta=j^{11/2}+1\) is not small** and is never used as small. The large scalar drift \(\int(v-\theta)\) is removed exactly. Uniformity over permitted past histories follows from the barrier and reset estimates; it does not require their previous words to belong to the current finite family.

## 5. Entire-leg removal, determinant normalization, and the exact targets

Let U,V be the diagonal fundamental scalar solutions over the up-ramp, dwell, down-ramp, and final rest, with initial data (1,0) and (0,1). For positive \(\lambda_i\), the identity \((e^{\int p}y')'=e^{\int p}\lambda_i y\) proves U positive and V nonnegative, with V positive after the initial point. Hence \(D=U+\theta V>0\) and \(0\le K=D^{-1}V\le\theta^{-1}I\), uniformly in the leg length. D and K depend on the fixed leg and a, not on h or the incoming history; \(K_h=0\).

The full transfer is

\[
 T_{lj}=(U+VP_e)B,\qquad
 D^{-1}T_{lj}=[I+K(P_e-\theta I)]B.
\]

This verifies the precise ordered identity. There is no conjugation of an error by D, and therefore no exponential condition-number cost from the long dwell. The exit graph and its h derivative differ from \(\theta I\) by \(O(C_N\eta)\); combining with section 4 gives C1 convergence after smooth determinant normalization. Determinants are positive: pulse and complete regular value maps have positive determinant, and D is positive diagonal.

For a cycle of length h, the underlying permutation has determinant \((-1)^{h-1}\), and its added wrap sign is \((-1)^{h-1}\). Thus \(\det\Pi_C=1\), including singletons, and the block sum belongs to SL. Unit-modulus signs preserve each cycle's coordinate support and all norm itineraries. They are needed for even-length cycles.

The source's local diffeomorphism at the specified target, restricted to a smaller finite parameter ball, persists under a sufficiently small C1 perturbation. Composing in a chart with its local inverse gives the stated contraction proof, uniformly for all incoming graphs satisfying section 3. At the selected parameter it yields exactly

\[
 T_{lj}=s_{lj}D_{lj}\Pi_l,\qquad s_{lj}>0,
\]

simultaneously on the active finite product. No limiting equality is substituted. Furthermore \(e^{-\int v}D^{-1}T_{lj}\) lies in a fixed compact neighborhood of positive determinant, so

\[
 \log s_{lj}=\int v+O_N(1),\qquad |\log s_{lj}|\le C_NT_j.
\]

For \(l=1\), the scalar pulse factor has logarithm \(O(T_j)\) from the global graph bounds. Even without using a small exit error, the leg ratio

\[
 \frac{U+VP_e}{U+V\theta}
\]

lies between 1 and \(P_e/\theta\). Its logarithm is bounded by the global positive scalar barriers, independently of the word level. This proves the asserted scalar estimate and positivity for \(E_1\) with \(\Pi_1=I\).

## 6. Countable chronological activation and all-order control

At level N all word, compact-parameter, local-inverse, tolerance, finite-degree error, and profile derivative constants through order \(N+2\) are finite. Taking a running maximum \(M_N\) and then a sufficiently large finite, strictly increasing integer \(J_N\) meets \(M_N\le j^{1/8}\), every finite inverse tolerance, and the geometric smallness conditions for **all** \(j\ge J_N\). No rate for \(J_N\) is required. Large cycle lengths or poor finite inverses merely delay a finite activation.

The preceding level remains operative in every period before the next threshold. Thus all old targets persist without waiting gaps; after \(j_l=J_{l-1}\), the same \(\Pi_l\) occurs at every later period even if the realizing word changes. The construction of h_j depends only on the earlier metric and the current finite problem. There is no future boundary condition. All degrees activate since each \(J_N\) is finite. The scalar cost is then bounded by \(j^{49/8}\) for every active block, with the \(l=1\) case eventually included as well.

The metric is defined on disjoint finite periods with flat joins and \(t_j\to\infty\). It needs no convergence of h_j and no limit of separate metrics. For each fixed derivative order k, sufficiently late levels control that order; pulse time derivatives carry the factors \(T_j^{-k-1}\), while the fixed ramps carry \(T_j^{-k}\). The \(j^{1/8}\) bound leaves them tending to zero. Spatial derivatives of the Hopf tensors are uniformly bounded at each fixed order because J ranges in a compact orthogonal-complex-structure family. Auxiliary J may jump between its disconnected components in an open round gap, where the actual metric is independent of J. This establishes local smoothness, all required derivative control, and smooth annular limits without an unbounded-degree inverse hypothesis.

## 7. Full Ricci tensor, geometry, AVR, and both cone limits

For \(g=dr^2+r^2\gamma(t)\), the shape endomorphism is \(S=r^{-1}(I+B)\), where \(B=bI+H\), \(H=(q'/2q)(P_J-I/m)\). Computing \(-\operatorname{tr}(\partial_rS+S^2)\) and \(\operatorname{Ric}_{r^2\gamma}^{\#}-\partial_r S-(\operatorname{tr}S)S\) gives exactly

\[
 r^2\operatorname{Ric}_{rr}=-m(b+b'+b^2)-\operatorname{tr}H^2,
\]
\[
 r^2\operatorname{Ric}_{T}^{\#}=\operatorname{Ric}_{\gamma}^{\#}-B'
                         -(m(1+b)-1)(I+B).
\]

The mixed term is the Codazzi divergence of S minus the differential of its trace. The trace is spatially constant. The Hopf field is Killing and of constant length for each Berger link, so its unit normalization has zero divergence and geodesic integral curves; consequently \(\operatorname{div}P_J=0\) and \(\operatorname{div}H=0\). This proves the mixed term is **zero**. On a round gap, it is also zero, and changing the J label there produces no metric derivative. Thus both orientation classes are covered and separate radial/tangential tests do establish the full tensor inequality in this particular construction.

In the round prefix the tangential expression equals

\[
 (m-1)(a^{-2}-1)-(2m-1)b-mb^2-b'
 \ge(m-1)(a^{-2}-1-2b-b^2)\ge0.
\]

This uses \(b+b'+b^2\le0\), \(a\le1\), and \(-1/4\le b\le0\). Radial Ricci is nonnegative there. The proof never invokes a strict link margin at the unit round core.

On active periods S1, its extension below q=1, and \(a\le\bar a\) give \(\operatorname{Ric}_\gamma^\#\ge(m-1+\epsilon)I\). All additional tangential terms tend uniformly to zero; fixed ramps have \(q'=O(j^{-6})\), \(q''=O(j^{-12})\), and weak pulses have bounds \(M_Nj^{-12}\), \(M_Nj^{-18}\). The radial buffer has order \(j^{-17/2}\). Ramp cost is \(O(j^{-12})\); pulse cost is at most \(O(M_N^2j^{-24})\le O(j^{-95/4})\). Each is smaller than the buffer. Finite thresholds make the complete Ricci tensor nonnegative everywhere and the active tangential block strictly positive.

The radial segment has length r, and any path from the center to coordinate r has length at least its radial variation r. Thus r is precisely geodesic distance. Smooth closed bounded coordinate balls are compact, proving completeness. The determinant of the Berger deformation cancels its \(q^{-1/m}\) factor, giving exactly \(r^ma(\log r)^m dr\,d\mathrm{vol}_0\). Its integral divided by \(\omega_{m+1}R^{m+1}\) tends to \(a_*^m\); this is an all-radius limit independent of all partitions and pulse parameters.

Choose centers deep inside successive round rests and Berger dwells. Their logarithmic distances to both boundaries tend to infinity, so every fixed logarithmic annulus is eventually wholly inside that constant-q piece. The derivatives of a tend to zero in every order; the annular limits are precisely the two links in S236. Inner balls of radius \(\epsilon\) have ambient diameter at most \(2\epsilon\) in both spaces via the center. Truncating to an annulus, then sending \(\epsilon\) to zero, includes the tips in pointed convergence. Uniform radial and angular bounds control the outer truncations as well.

The auxiliary sectional-curvature statement in AUTHOR-PROOF line 200 is correct: for the unscaled Berger metric \(g_H+q\eta^2\), the Hopf-horizontal curvature is q, and the horizontal curvature is \(1+3(1-q)\langle JX,Y\rangle^2\); on a horizontal J-plane it is \(4-3q\). These follow by the connection/submersion calculation for a unit Hopf field. The common scaling multiplies them by \(a^{-2}q^{1/m}\). Alternatively the directly read source Ricci eigenvalues already differ by \(a^{-2}q^{1/m}(m+1)(q-1)>0\). Hence the Berger link is nonround and cannot be isometric to the round link. An isometry of pointed cones identifies their unit distance spheres; their tips are also intrinsically distinguished singular cone vertices, since these strict-link-Ricci cones are not Euclidean at their apex. Both the stated cone limits and nonisometry follow.

## 8. Signed whole-leg endpoint estimate

Fix l, allowing constants to depend on it but not on the subsequent level. On a dwell, with \(A=\mu/\delta>0\), the exact coefficients are

\[
 \lambda_i(t)=\lambda_i^*e^{-2A(1+t)^{-\delta}},\quad
 p(t)=p_0-m\mu(1+t)^{-1-\delta},\quad
 \lambda_i^*=d_i(d_i+p_0)>0.
\]

For the positive root \(\rho^2+p\rho=\lambda\), the derivatives are \(\rho_\lambda=(2\rho+p)^{-1}\) and \(\rho_p=-\rho/(2\rho+p)\). Therefore

\[
 \rho_i=d_i-\frac{2A\lambda_i^*}{2d_i+p_0}(1+t)^{-\delta}
        +O_l((1+t)^{-2\delta})+O_l((1+t)^{-1-\delta}).
\]

The drift from the decrease of p is positive, but of the last, smaller order. It cannot cancel the strictly negative leading correction. Each fixed finite block has a positive minimum of the leading coefficients. Differentiating the implicit equation gives \(\rho_i'=(\lambda_i'-p'\rho_i)/(2\rho_i+p)=O_l((1+t)^{-1-\delta})\). This verifies both the sign and the derivative bound, not just convergence to d_i.

For the reference solution defining D, \(w=y'/y\) starts at \(\theta_l\) and has positive upper and lower scalar barriers throughout the complete leg. On the dwell \(z=w-\rho_i\) satisfies exactly

\[
 z'=-(p+w+\rho_i)z-\rho_i'.
\]

Uniform damping and a bounded, not assumed small, entrance mismatch give

\[
 \int_{\rm dwell}|z|\le C_l(1+L_jt_j^{-1-\delta}).
\]

Here \(L_jt_j^{-1-\delta}=O(j^{-3/2})\). The two ramps and rest together have length \(3T_j\) and bounded w, so their complete contribution is \(O_l(T_j)\). Since \(L_jt_j^{-\delta}\asymp j^{13/2}\), both inequalities (8.6) follow for the **entire** leg:

\[
 L_jd_i-C_l(j^{13/2}+T_j+1)
 \le\log(D_{lj})_{ii}
 \le L_jd_i-c_lj^{13/2}+C_l(T_j+1).
\]

This is the precise endpoint input. Replacing it by an epsilon-growth statement would lose the conclusion, but no such replacement is used.

## 9. Cycle products, every-radius interpolation, and the exponent 15/16

For any fixed finite cycle, its mean-zero root itinerary has bounded partial sums, with a constant allowed to depend on the finite cycle. Abel summation against \(j^7\) yields

\[
 \sum_{j=j_l}^{J} j^7d_{i(j)}
   =\mu_C\sum_{j=j_l}^{J}j^7+O_l(J^7).
\]

No bound on cycle length uniform in l is needed. Constants may grow arbitrarily with a fixed prescribed block; the eventual growth threshold absorbs them.

The negative sum is \(\sum j^{13/2}\asymp J^{15/2}\). The absolute scalar sum is at most \(\sum j^{49/8}=O(J^{57/8})\), and complete ramp/rest and weighted-cycle errors are \(O_l(J^7)\). The strict order

\[
 15/2=60/8>57/8>7
\]

leaves a positive negative-drift coefficient for each fixed l. Replacing \(\sum j^7\) by endpoint time costs \(O(J^7)\), since \(t_{J+1}=\sum_{j\le J}j^7+O(J^7)\) and \(t_{J+1}\asymp J^8\).

Every exact period matrix is a positive scalar times a positive diagonal times the same signed cycle permutation. Products remain monomial. Distinct starting coordinates have distinct final supports, so the minimum and maximum column lengths bound **every** nonzero starting vector. The lower initial constant is positive by invertibility; it need not have a uniform lower bound over all vectors. The upper and lower halves of (8.6), together with the absolute scalar estimate, give both halves of (9.2).

For a partial period, the global Riccati norm bound costs at most \(O_l(j^7)\), and replacing an endpoint \(\mu_Ct_j\) by \(\mu_Ct\) has the same cost. This is smaller than \(j^{15/2}\). Thus, at every sufficiently large t,

\[
 c_Ye^{\mu_Ct-C_lt^{15/16}}
 \le\|Y(t)\|
 \le C_Ye^{\mu_Ct-c_lt^{15/16}},\qquad c_l>0.
\]

The exponent is actually \((15/2)/8=15/16\), not merely some unspecified o(t) correction. On fixed \(V_l\), round L2 norm is the coefficient norm, and

\[
 \|Y\|/\sqrt{\operatorname{Vol}S^m}\le\|u\|_\infty
 \le\sqrt{N_l/\operatorname{Vol}S^m}\,\|Y\|.
\]

The sphere is the actual geodesic sphere since r is distance. Taking logarithms proves S4, while the upper bound proves S5 and exact endpoint membership. The compact remaining region is absorbed into the allowed individual constant.

For \(E_1\), the itinerary is constant, all roots coincide, and the scalar estimate in section 5 gives exactly the same sums without Abel summation. Its real dimension is \(m+1\). Within a fixed l, different cycles have disjoint endpoint supports, including when means coincide. Across l, round L2 orthogonality holds at every sphere. The endpoint lower bounds and partial-period norm bounds exclude cancellation for any nonzero finite sum, whose exact exponent is the maximum of its present exponents. Adding a constant does not change a positive exponent. No zero-supremum or shared-mean exception remains.

## 10. Exhaustion of the full harmonic filtration for every real d

Let u be an arbitrary smooth global harmonic function of pointwise growth at most a real \(d\ge0\). Each individual coefficient is obtained by integration against a fixed smooth round spherical harmonic. Differentiation on a compact sphere is justified by smoothness. Self-adjointness with respect to the fixed round measure follows from the spatially constant angular volume factor and the exact invariant angular operator. Thus each coefficient solves the displayed block ODE without differentiating an infinite series.

On the Euclidean core its regular branch is \(Y_l=r^lv_l\); smoothness excludes the singular branch. The l=0 projection is constant. Each nonzero l projection is consequently on the global center-regular graph. The pointwise bound gives

\[
 \|Y_l(t)\|\le\sqrt{\operatorname{Vol}S^m}A_u(1+e^t)^d,
\]

whereas a fixed nonzero coefficient at \(t_0\) gives \(\|Y_l(t)\|\ge\|Y_l(t_0)\|e^{cl(t-t_0)}\). If \(cl>d\), this is impossible as \(t\to\infty\), irrespective of how small the fixed initial coefficient is. All such projections vanish identically. There are only finitely many remaining degrees. Round L2 completeness identifies u with their finite sum on each sphere, and smoothness makes this pointwise equality.

Within each remaining degree, the invertible value map at activation pulls back the direct sum of all prescribed cycle supports. Therefore every regular solution decomposes into those E spaces. Section 9 shows that a finite sum containing a mean \(>d\) cannot have growth at most d. Conversely each mean \(\le d\) satisfies the endpoint upper bound and hence the d bound. This proves both inclusions and the directness of S3 at **every real d**, including every equality case. The graph lower bound and exact exponent imply \(\mu_C\ge cl\), so the right side is finite independently as claimed. For \(d=0\), only constants remain.

The real dimensions follow from invertible regular initial-value maps: \(|C|\) and \(m+1\). Triangle inequalities between two fixed basepoints multiply growth constants by a finite factor for every real \(d\ge0\). The stated Euclidean formula is the usual sum of real harmonic polynomial dimensions through integer k, with the second binomial zero at k=0; for real d it is evaluated at \(\lfloor d\rfloor\). There is no altered Euclidean normalization.

## 11. Explicit nonvacuity and genuinely different filtrations

For \(m=7\), \(q\in[1,101/100]\), the lesser factor in S1 is \(1-(q-1)/3\). Hence

\[
 q^{1/7}[1-(q-1)/3]\ge299/300>9/10=a_*^2
\]

throughout the entire interval, not only at its endpoints.

In \(V_2(S^7)\), \(B_2=16\) and \(N_2=35\). Holomorphic quadratics on \(\mathbb C^4\) have complex dimension 10, and their conjugate pair gives real dimension 20 at charge-square 4. Trace-free Hermitian quadratics give real dimension 15 at charge 0. Since \(q_*^{-1}-1=-1/101\), the charge-four root is strictly smaller. A two-cycle containing one real coordinate of each type has mean strictly between the two roots and dimension two; the singleton prescription instead has one dimension at each old endpoint for these two coordinates.

The \(l=1\) bracket is \(6+100/101\), strictly smaller than \(16-4/101\). For \(l\ge3\), every bracket is at least \(l(l+6)-l^2/101\), an increasing function there, and its value at 3 is \(27-9/101>26>16\). The positive-root function is strictly increasing. Thus no other singleton degree can account for the inserted mean, and no overlap from E1 is hidden. Leaving all other degrees and coordinates singleton in both prescriptions produces different numerical dimension functions, not just different named subspaces on different metrics. The ambient dimension is 8 and AVR is \(a_*^7=(9/10)^{7/2}\). This verifies the frozen example and its comparison convention exactly.

## 12. Concrete objections, resolutions, alternatives, and remaining obligations

The following were substantive challenges to certification, not assumed away:

| Potential obstruction | Resolution in the submitted scope |
|---|---|
| A's headline only supplies a finite counterexample; arbitrary product targets might be unavailable. | Its actual algebra and `prop:word` give the required finite product-SL local diffeomorphism, including degree-dependent factors, signs, and both orientations. |
| The radial power could be undefined near the center, or the first reset could be missing. | The formula is explicitly restricted to t>B; the Euclidean/round prefix precedes all late activations and supplies the first rest. |
| Noncommuting P and A could invalidate scalar barrier language. | The first-contact eigenvector calculation proves the matrix barriers without commutation, from the displayed Riccati equation. |
| A slower tail might produce a large pulse error \(T\eta\). | The exact scalar baseline retains that drift; the explicit residual and its differentiated damping equation have integrated size \(O(C_N\eta)\). |
| A long diagonal leg could amplify an off-diagonal error or spoil the inverse theorem. | The ordered identity removes the whole leg on the left, with bounded K and zero current-parameter derivative of K. No D conjugation occurs. |
| Even cycles might have the wrong determinant or old targets might drift. | The wrap sign makes every cycle determinant one; the identical target is solved exactly at every later period, including across level changes. |
| Countable activation might require a limit of control parameters or a uniform inverse radius. | Only finitely many parameters/constants enter each chronological period; finite thresholds and locally finite flat gluing suffice. |
| Coordinate Ricci signs might miss a mixed block. | The constant-length Killing Hopf field has divergence-free projection, giving a genuinely zero mixed block, including round orientation resets. |
| The p drift or entrance mismatch might reverse the signed endpoint deficit. | The p contribution is order \(t^{-1-\delta}\), while the strictly negative a contribution is order \(t^{-\delta}\); damping integrates the bounded mismatch to O(1). |
| Exact rate might not imply critical membership, especially inside unfinished cycles. | The negative \(J^{15/2}\) term exceeds \(J^{57/8}\) and \(J^7\), including every partial period; it yields the stated negative \(t^{15/16}\) correction. |
| A tiny infinite tail or equal-mean cancellation could evade classification. | Every fixed nonzero high-degree coefficient violates the uniform cl lower bound; exact monomial supports and orthogonality prevent the remaining finite cancellations. |
| The explicit freedom might be vacuous or masked by another degree. | S1 and the real 20/15 multiplicities and strict degree separation were checked directly above. |

The expanded residual calculation, initial scalar-baseline datum, contact-vector interpretation, first-prefix reset, scalar \(l=1\) leg ratio, and curvature/nonisometry calculations are **clarifications entailed by the text and its explicit source definitions**. They do not change the metric, hypotheses, schedule, transfer target, root, or growth conclusion, and do not insert a new solvability or compactness theorem. In particular, I have not substituted an approximate transfer, a finite truncation, or an epsilon-growth endpoint for the submitted claims.

The strongest relevant alternatives were considered at their actual scope. Source B already has infinite high-mode graphs, countable matching, and global/every-radius traces at fixed finite rank; treating them as absent would be wrong. They do not themselves supply S236's varying finite product targets, but S236 avoids requiring that extension of B. The admitted I130/I133 mathematics includes finite simultaneous bands, countable geometry with mixed Ricci paid, fixed-cutoff terminal forgetting, and actual geometric examples showing that local metric convergence, a common core, and even uniform AVR tails need not preserve normalized growth constants. The admitted H manuscript develops nonuniform graphs, finite quotients, shared controls, triangular lifts, and all-radius scheduling for its different sparse R3 question. Those operations have been read at the extents recorded in the access report; its truth is not stipulated and it is neither a premise nor a theorem regraded here. S236 instead retains exact global functions from core data and exact old targets, so it does not rely on the compactness inference those examples refute.

The primary comparisons also do not replace any proof step. Huang's read unique-cone results have their unique-cone hypothesis and distinguish logarithmic degree from critical endpoint membership. Xu's relevant three-circles hypothesis is \(\alpha\notin D(M)\), confirmed visually; the text extraction's corrupted glyph is not a less-than condition. The continuous cone-root branches along S236's slow ramps all meet at the round root, so their connected union contains every cycle mean. Thus the author's auxiliary cone-spectrum comparison is consistent and does not assert roots outside that spectrum. CM98 Theorem 0.26 has finite dimensional constants \(C_1,C_2\), not a sharp coefficient-one asymptotic; its corrected theorem and proof crops were checked. Colding–Naber's actual fixed-volume slow-link curvature balance and Perelman's oscillatory link construction are relevant precedents, but neither an unread smooth-cap argument nor imported external proof is needed by this explicit construction. No literature-wide conclusion is made.

The retained Lean endpoint's `main` is obtained from `axiom mainStatement : MainClaim`; it supplies no proved formal coverage, and none is claimed for S236. Artifact verification, including the copied controls, is not a mathematical gate.

**Remaining essential mathematical obligations for this correctness review: none identified.** The stated access limits do not leave a used premise or an essential step unresolved: both operative upstream papers were read, their truth is stipulated, and every source-to-S236 modification and auxiliary scope assertion needed here has been checked above. The recommendation remains PASS for the entire original statement and proof, subject only to the parent's independent adoption procedure, with no contribution disposition.
