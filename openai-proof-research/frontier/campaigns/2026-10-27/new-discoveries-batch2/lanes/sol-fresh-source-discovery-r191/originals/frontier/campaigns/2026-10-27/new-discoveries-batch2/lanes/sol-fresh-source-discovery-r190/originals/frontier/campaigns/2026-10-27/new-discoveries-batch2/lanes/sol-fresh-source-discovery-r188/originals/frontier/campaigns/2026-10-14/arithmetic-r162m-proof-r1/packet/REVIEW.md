# Independent full correctness review — Arithmetic162m ROUND1

**Verdict: PASS for the entire unchanged frozen theorem and author proof, relative to the stipulated upstream truth.** No necessary author correction or unpaid essential correctness operation remains. This is solely a correctness verdict. The other review was not consulted. The mathematical justification below is an independent reconstruction, not an adoption of the author-check assertions.

The reviewed statement concerns every finite real p>3, every nonempty compact smooth embedded definite-curvature two-surface in R³ (including smooth boundary and disconnected descriptions), and every normalized complex Lp extremizing sequence. The conclusion is strong subsequence convergence after the stated plus-sign modulations, attainment, and qualitative stability relative to all normalized extremizers. None of these quantifiers is restricted in this verdict. No uniformity in the surface, endpoint, rate, or identification of extremizers is being inferred.

## 1. Applicable paid estimate and all exponent choices

Write μ=σ, m=μ(Σ), T=EΣ, and U_a h(ξ)=exp(−2πi a·ξ)h(ξ). A nonempty smooth embedded two-surface has 0<m<∞: any interior local patch has positive area (a boundary chart also contains interior points), and finitely many relatively compact smooth charts have finite total area. Compactness supplies a finite frequency radius RΣ=supΣ|ξ|.

The operative graph estimate is stronger than the diagonal headline: it has L³ input and Lq output for every q>3. The actual proof provides the range 3<q≤4 and then the range q>4 by interpolation with the elementary L∞ output bound on a fixed compact frequency window. Thus its use at an exponent smaller than p is legitimate; it is not an inference from boundedness Lp→Lp alone.

The chart application retains L³ input. To make that explicit, partition Σ into finitely many measurable pieces subordinate to its smooth charts. On a piece let ξ=v+L(ζ,φ(ζ)), with invertible fixed L and induced area density J(ζ)>0. The actual source construction extends the smooth graph at boundary points and embeds a sufficiently small elliptic graph germ into an admissible phase, including its transition region. A local normal may be reversed to make the Hessian positive definite; no globally chosen normal is needed. Set g(ζ)=f(ξ(ζ))J(ζ) on the chart piece and zero elsewhere. Then

\[
\|g\|_3^3=\int_{\mathrm{piece}}|f|^3J^2\,d\mu
\le(\sup J)^2\|f\|_{L^3(\mathrm{piece})}^3,
\]
\[
T(f1_{\mathrm{piece}})(x)=e^{2\pi i x\cdot v}E_\phi g(L^Tx),\qquad
\|E_\phi g(L^T\cdot)\|_q=|\det L|^{-1/q}\|E_\phi g\|_q.
\]

Where the source theorem is phrased with terminal windows, its finite smooth square partition is used: g=Σν(gχν)χν, and each gχν has L³ norm at most a fixed multiple of ||g||₃. Equivalently one can subdivide where a window is bounded below. Zero extension and window multiplication require no smoothness or trace of g. The graph estimates explicitly admit complex rough data. Finite summation therefore gives

\[
\tag{A} \|Th\|_q\le A_q\|h\|_3\quad(3<q<\infty).
\]

All chart, determinant, window, curvature, and derivative constants may depend on this fixed Σ. There is no passage to a family of degenerating surfaces. Boundary is a condition on the supporting set, not an input trace constraint; disconnected pieces are handled by the same finite sum.

Since ||h||₃≤m^{1/3−1/p}||h||p, A at q=p proves C:=||T||p→p<∞. Also T1(0)=m and T1 is continuous, so it is nonzero on a ball. A puts T1 in Lp, whence C>0.

For any fixed p>3 choose

\[
q_0=(p+3)/2,\qquad s=4q_0/3=2+2p/3,\qquad q_1=p+s+1.
\]

Then 3<q₀<p<q₁, s<q₁, all exponents are finite, and s>4. Interpolating T:L¹→L∞ (norm ≤1) with A at q₀, with weight 3/4 on the L³ endpoint, gives

\[
1/2=(1-3/4)/1+(3/4)/3,\quad 1/s=(3/4)/q_0,
\quad \|Th\|_s\le K\|h\|_2,
\]

where K can be taken to be A_{q₀}^{3/4}. These are compatible realizations of the same integral operator, initially on bounded functions. Its L² extension agrees with its integral definition: approximation in L² also gives L¹ convergence on the finite measure space, hence uniform convergence of the defining transforms, and a subsequence of the Ls limit agrees almost everywhere. Moreover ||Th||∞≤√m||h||₂. Interpolating these two output norms gives T:L²→Lq₁.

For 3<p<4 there is no L²→Lp claim: s>4>p. For 4≤p<6 one still has s>p; at p=6, s=p; for p>6, s<p. The same choice q₁>max(p,s) handles every case without change. Finally

\[
\theta=\frac{1/p-1/q_1}{1/q_0-1/q_1}\in(0,1)
\]

will interpolate output norms between q₀ and q₁ to p. No endpoint estimate, even-integer identity, or input exponent 2 normalization of extremality is used.

## 2. Elementary dependencies, including complex data

For h∈L¹(μ),

\[
|Th(x+y)-Th(x)|\le2\pi R_\Sigma\|h\|_1|y|.
\]

Thus every such transform is uniformly continuous. If h is bounded, A at q₀ puts Th in a finite Lq₀. A uniformly continuous finite-Lr function on R³ vanishes at infinity: a sequence of points going to infinity where its modulus exceeds ε would, by uniform continuity, give infinitely many disjoint balls of one fixed radius with modulus at least ε/2, contradicting finite integral. Bounded truncations h_M approximate every L¹ density in L¹, and ||T(h−h_M)||∞≤||h−h_M||₁. Consequently

\[
\tag{B} Th(x)\longrightarrow0\quad(|x|\longrightarrow\infty),\qquad h\in L^1(\mu).
\]

This argument does not require a quantitative stationary-phase theorem at a boundary. For h∈Lr, 1<r<∞, and b∈Lr′, h\bar b∈L¹. Therefore the pairing of U_a h with b tends to zero as |a|→∞ by B, so U_a h⇀0 in Lr. If a_n→a, dominated convergence proves U_{a_n}h→U_a h strongly in every finite Lr. For a bounded weakly convergent sequence, varying a dual test by a strongly convergent modulation preserves the limiting pairing. This last fact will exclude bounded differences of extraction parameters.

Weak convergence in L² or Lp implies pointwise convergence of transforms at every fixed x, because the kernel exp(−2πi x·ξ) is in the corresponding dual space on Σ. Conjugations depend only on the convention for the dual pairing and do not change the assertion.

The output splitting used below requires only the following identity. If v_n→v almost everywhere and sup||v_n||r<∞ for 1<r<∞, then

\[
\tag{C} \|v_n\|_r^r-\|v_n-v\|_r^r\longrightarrow\|v\|_r^r.
\]

Here is a proof with the needed hypotheses. Fatou gives v∈Lr and hence a_n=v_n−v is bounded in Lr. The real differentiability bound for z↦|z|r on C≅R² and Young's inequality give, for every ε>0,

\[
\big||a+b|^r-|a|^r\big|\le\epsilon|a|^r+K_{r,\epsilon}|b|^r.
\]

The nonnegative function

\[
\left(\big||v_n|^r-|a_n|^r-|v|^r\big|-\epsilon|a_n|^r\right)_+
\]

is bounded by (K_{r,ε}+1)|v|r and tends to zero pointwise. Dominated convergence bounds the limsup of the integral of the absolute defect by ε sup||a_n||r^r. Letting ε decrease to zero proves C. This covers all three exponents q₀,p,q₁, including nonintegral p, without any input almost-everywhere convergence.

For h∈L¹, the measure hμ is compactly supported. Expanding exp(2πi z·ξ) about any z₀∈C³ gives an absolutely locally uniformly convergent power series under the integral; its terms are dominated by ||h||₁ exp(2πRΣ|z−z₀|) up to an equivalent fixed norm. Thus Th is entire in complex variables and real analytic on R³. If it vanishes on a real open ball, all real derivatives at its center vanish, and the same global Taylor series gives Th≡0. In that event ∫ξ^α h dμ=0 for every multi-index α. Complex polynomials in the real coordinate restrictions contain constants, separate the points of the compact set Σ, and are closed under conjugation. Stone–Weierstrass gives uniform density in C(Σ). Hence hμ annihilates all continuous functions and is the zero finite complex measure, so h=0 almost everywhere.

It follows that two nonzero L¹ densities have transforms simultaneously nonzero on an open ball. Indeed, the nonzero set of the first is a nonempty open set, and the zero set of the second has empty interior; choose a common nonzero point and use continuity. This is valid for complex functions with cancellation, for boundary surfaces, and for disconnected Σ. Connectedness relevant to analytic continuation is that of the output R³; connectedness of Σ is unnecessary.

## 3. Extraction with one subsequence and precise residual control

Let ||f_n||p=1, with no extremality assumption yet. Put M₂=m^{1/2−1/p}. Finite measure gives ||f_n||₂≤M₂ and ||f_n||₃≤m^{1/3−1/p}. By A and the L² estimates, all three output norms q₀,p,q₁ are bounded. Select a subsequence on which ||f_n||₂²→A²≤M₂² and each output norm to its exponent tends to a limit L_r, r∈{q₀,p,q₁}.

Inductively maintain nonzero profiles φ_j, parameters a_n^j with pairwise differences going to infinity, and residuals

\[
r_n^J=f_n-\sum_{j=1}^J U_{a_n^j}\phi_j,
\]

with the following properties on the current nested subsequence:

\[
U_{-a_n^j}r_n^J\rightharpoonup0\text{ in }L^2\quad(j\le J),\qquad
\|r_n^J\|_2^2\longrightarrow A^2-\sum_{j\le J}\|\phi_j\|_2^2,
\]
\[
\phi_j\in L^p,\quad U_{-a_n^j}f_n\rightharpoonup\phi_j\text{ in }L^p,
\quad\|\phi_j\|_p\le1,
\]
\[
\tag{D_J}
\|Tr_n^J\|_r^r\longrightarrow L_r-\sum_{j\le J}\|T\phi_j\|_r^r
\quad(r=q_0,p,q_1).
\]

At J=0 the assertions hold. At any finite stage, the residual L² limit is at most M₂², so after dropping finitely many terms ||r_n^J||₂≤B:=2M₂+1. The value of B is independent of J; the dropped prefix can depend on J. Also the residual belongs to Lp and has the finite bound 1+Σ_{j≤J}||φ_j||p. This bound is not asserted to be uniform in J.

Let η_J=limsup||Tr_n^J||q₁ on the current subsequence. Its finiteness follows from the L²→Lq₁ estimate. If it is zero, stop. Otherwise select a subsequence attaining the limsup, with output norm at least η_J/2 and input L² norm at most B. The elementary integral inequality

\[
\|Tr_n^J\|_{q_1}^{q_1}\le
\|Tr_n^J\|_\infty^{q_1-s}\|Tr_n^J\|_s^s
\le\|Tr_n^J\|_\infty^{q_1-s}(KB)^s
\]

implies the existence of a_n^{J+1} with

\[
|Tr_n^J(a_n^{J+1})|\ge c\eta_J^{\gamma},\qquad
\gamma=q_1/(q_1-s)>0.
\]

For example c=2^{-1-q₁/(q₁−s)}(KB)^{-s/(q₁−s)} works when K>0; positivity of T implies K>0. Choosing an approximate supremum is enough. Since

\[
\int_\Sigma U_{-a_n^{J+1}}r_n^J\,d\mu=Tr_n^J(a_n^{J+1}),
\]

a weakly convergent L² subsequence has limit φ_{J+1} satisfying

\[
\tag{E} \|\phi_{J+1}\|_2\ge c\,m^{-1/2}\eta_J^\gamma>0.
\]

The complex scalar integrals converge along weak convergence; their moduli remain bounded below. It is unnecessary to make those scalars real or positive, or to add a scalar-phase symmetry.

For each of the finitely many old parameters, refine so that the difference with the new parameter either diverges in norm or converges to a finite vector. In the second case the new frame is a strongly convergent modulation composed with an old frame. The old-frame residual converges weakly to zero, so the new limit would be zero, contrary to E. Thus all new differences diverge. Define r_n^{J+1}=r_n^J−U_{a_n^{J+1}}φ_{J+1}. Expanding its L² square and using the defining weak limit gives

\[
\|r_n^{J+1}\|_2^2=\|r_n^J\|_2^2-\|\phi_{J+1}\|_2^2+o(1).
\]

In the new frame the new residual has weak limit zero by construction; in an old frame the subtracted profile tends weakly to zero by B. This establishes the Hilbert invariants at the next stage.

Lp membership must be proved separately. The ORIGINAL sequence U_{-a_n^{J+1}}f_n has Lp norm one; by reflexivity it has a further weak Lp limit ψ. The continuous inclusion Lp↪L² implies weak convergence in L² as well: every L² test belongs to Lp′ because p>2 and m<∞. Each old profile in the new frame tends weakly to zero in L² by separation. Consequently ψ equals the L² residual limit φ_{J+1}. It follows that φ_{J+1}∈Lp and ||φ_{J+1}||p≤1. This proves the original-sequence weak Lp limit, rather than trying to obtain it from a uniform residual Lp estimate.

For this fixed finite J, A bounds Tr_n^J in Lq₀,Lp,Lq₁, since its Lp norm is bounded by a finite sum. In the new frame,

\[
T(U_{-a_n^{J+1}}r_n^J)(x)=Tr_n^J(x+a_n^{J+1})\longrightarrow T\phi_{J+1}(x)
\]

at every x. Apply C at each of the three exponents and use invariance of Lebesgue measure under translation. The difference of these outputs is exactly T(U_{-a_n^{J+1}}r_n^{J+1}). Thus

\[
\|Tr_n^J\|_r^r=\|T\phi_{J+1}\|_r^r+\|Tr_n^{J+1}\|_r^r+o(1).
\]

This proves D_{J+1}, including existence of its output limits, by induction. No Brezis–Lieb application involves an unbounded-in-n residual; the bound is allowed to depend on the fixed J.

If the process is infinite, its Hilbert identities give Σ_j||φ_j||₂²≤A². Summing E squared therefore yields

\[
\sum_{J\ge0}\eta_J^{2\gamma}\le c^{-2}m A^2<\infty,
\]

so η_J→0. The η_J are the values at their own nested stages; D_J ensures those stage limits persist on all later subsequences. Even without using equality of these limits, a final tail contained in the stage sequence has limsup at most η_J.

For precision about a single subsequence, denote the infinite nested index sets by I_J. Enumerate all finite-stage norm identities, all finite-stage L² weak-zero and Lp weak-profile assertions tested against fixed countable dense subsets of L² and Lp′, and all parameter-separation assertions. These spaces are separable for finite exponents on this compact finite measure space. At step k choose an original index n_k>n_{k−1} in a sufficiently late tail of I_k, after all profiles occurring in the first k enumerated conditions have been defined (one may instead increase the stage index to include them). Require the finitely many scalar-limit errors to be at most 1/k and the finitely many separations to exceed k. Their convergence on the retained subsequence makes this possible. Define a_{n_k}^j only once j is present; fill its finitely many unused early values arbitrarily. Uniform boundedness in n for each fixed sequence upgrades convergence on dense tests to weak convergence for every test. The original modulations have Lp norm one; each fixed residual has a finite Lp bound and an eventual common L² bound, so this upgrade is justified. Every fixed J identity and separation consequently holds on this one strictly increasing sequence n_k.

For a finite extraction, use the final nested subsequence. For an empty extraction, retain the original selected subsequence and the residual f_n. In the finite case one can repeat the last residual for all larger J and insert zero profiles if desired. In every case we have

\[
\tag{F} \lim_{J\to\infty}\limsup_k\|Tr_{n_k}^J\|_{q_1}=0,
\]

with the stated convention in the finite case.

The essential uniform estimate is on OUTPUTS. D_J at q₀ and nonnegativity of the subtracted terms imply, for every fixed J,

\[
\limsup_k\|Tr_{n_k}^J\|_{q_0}\le L_{q_0}^{1/q_0}
\le A_{q_0}m^{1/3-1/p}=:M_0.
\]

Now apply output Hölder interpolation before taking limits:

\[
\limsup_k\|Tr_{n_k}^J\|_p
\le M_0^\theta\left(\limsup_k\|Tr_{n_k}^J\|_{q_1}\right)^{1-\theta}.
\]

F proves

\[
\tag{G} \lim_{J\to\infty}\limsup_k\|Tr_{n_k}^J\|_p=0.
\]

This establishes precisely the claimed remainder assertion. It requires neither sup_{n,J}||r_n^J||p<∞ nor input p-power decoupling. It does not interchange the limits in n and J or assert smallness with J varying arbitrarily with n. Those stronger assertions are unnecessary.

## 4. Weighted square mass and its equality case

Relabel the final subsequence by n. Since |||f_n|²||_{p/2}=1 and p/2>1, pass to a further subsequence such that |f_n|²⇀ρ in L^{p/2}. Positivity of the weak limit follows by testing against nonnegative bounded functions, and weak lower semicontinuity gives ||ρ||_{p/2}≤1. All previous assertions persist under this further subsequence.

Fix any finite J and bounded nonnegative measurable w. Expanding the nonnegative quantity ∫w|r_n^J|² gives four types of terms. The original square tends to ∫wρ, because w belongs to L^{p/(p−2)}. Each original/profile cross term tends to ∫w|φ_j|² by the original-frame weak Lp convergence: wφ_j∈Lp′, since p>2, φ_j∈Lp, and m<∞. The profile square is exactly ∫w|φ_j|², since modulations have modulus one. For j≠k, the cross term between two profiles is the transform of the single fixed L¹ density wφ_j\bar φ_k at a_n^k−a_n^j, hence tends to zero by B. Integrability also follows directly from φ_j,φ_k∈L². Taking the real parts in the expansion therefore gives

\[
0\le\int w\rho-\sum_{j\le J}\int w|\phi_j|^2.
\]

The convergence for all w is part of weak convergence itself; it does not require extracting an uncountable intersection of subsequences. Taking w to be indicators proves S_J:=Σ_{j≤J}|φ_j|²≤ρ almost everywhere. For example, if S_J>ρ on a set of positive measure, a positive-measure set where S_J−ρ>1/l for some l contradicts that indicator test. Union the null sets for the countably many J, and then use monotone convergence. We obtain

\[
\tag{H} S:=\sum_{j\ge1}|\phi_j|^2\le\rho\text{ a.e.},\qquad
\int S^{p/2}\,d\mu\le\int\rho^{p/2}\,d\mu\le1.
\]

This proves the full local square-mass assertion. No independence, equidistribution, nonresonance, or joint distribution of three or more phases has entered. Pairwise differences suffice exactly because the expanded expression is quadratic. The later p/2 power is taken after the limiting local inequality, not by asserting a higher-order oscillatory expansion.

Now assume ||Tf_n||p→C. D_J at p and G give

\[
\tag{I} C^p=\sum_j\|T\phi_j\|_p^p.
\]

The empty case is impossible because C>0. Since t=p/2>1, nonnegative finite sums satisfy Σb_j^t≤(Σb_j)^t. The countable version follows by monotone convergence. Together with H and the sharp operator norm inequality, it yields

\[
C^p=\sum_j\|T\phi_j\|_p^p
\le C^p\sum_j\|\phi_j\|_p^p
=C^p\int\sum_j|\phi_j|^p
\le C^p\int S^{p/2}\le C^p.
\]

All quantities are finite and all inequalities are equalities. In particular Σ_j||φ_j||p^p=1. The nonnegative defects C^p||φ_j||p^p−||Tφ_j||p^p sum to zero, so every nonzero φ_j attains its own norm inequality. Also the nonnegative integrable function S^{p/2}−Σ_j|φ_j|p has zero integral, hence is zero almost everywhere.

For any fixed two indices j≠k, if |φ_j|²=a>0 and |φ_k|²=b>0 at a point where S<∞, then

\[
S^t-\sum_l|\phi_l|^{2t}\ge (a+b)^t-a^t-b^t>0.
\]

The first inequality follows by grouping this pair and using superadditivity for the remaining nonnegative terms. It contradicts the almost-everywhere equality. Thus |φ_j||φ_k|=0 almost everywhere for every distinct pair, and a countable union of null sets suffices. This step is essential: scalar equality Σ||φ_j||p^p=1 alone would allow several profiles.

## 5. Excluding two disjoint extremizers, strong convergence, and signs

Suppose two nonzero profiles φ,ψ remain. Their disjoint supports imply

\[
\|\phi+\psi\|_p^p=\|\phi-\psi\|_p^p
=\|\phi\|_p^p+\|\psi\|_p^p.
\]

Both are exact extremizers individually, so the operator norm inequalities applied separately to φ+ψ and φ−ψ imply

\[
\tag{J}
\frac{\|T\phi+T\psi\|_p^p+\|T\phi-T\psi\|_p^p}{2}
\le\|T\phi\|_p^p+\|T\psi\|_p^p.
\]

For arbitrary complex u,v, convexity and the parallelogram identity give

\[
\frac{|u+v|^p+|u-v|^p}{2}
\ge\left(\frac{|u+v|^2+|u-v|^2}{2}\right)^{p/2}
=(|u|^2+|v|^2)^{p/2}
\ge|u|^p+|v|^p.
\]

The last inequality is strictly greater whenever u and v are both nonzero, because p/2>1. This strictness is independent of their complex arguments; even when the first convexity step is an equality, the last remains strict. By the analytic/injective result in §2, Tφ and Tψ overlap on an open ball. The scalar difference is a continuous positive function there and nonnegative everywhere. It is integrable, since all four outputs lie in Lp. On a smaller ball it has a positive lower bound; hence its integral is strictly positive. This contradicts J.

There is therefore exactly one nonzero profile φ. From I, ||Tφ||p=C. From the equality chain, ||φ||p=1. Its original-frame weak convergence is

\[
h_n:=U_{-a_n}f_n=e^{2\pi i a_n\cdot\xi}f_n\rightharpoonup\phi\quad\text{in }L^p,
\qquad\|h_n\|_p=\|\phi\|_p=1.
\]

For completeness the uniform convexity step has the right direction and constants for complex functions. Pointwise, with t=p/2≥1,

\[
|h+k|^p+|h-k|^p
\le (|h+k|^2+|h-k|^2)^t
=2^t(|h|^2+|k|^2)^t
\le2^{p-1}(|h|^p+|k|^p).
\]

After division by 2^p and integration this is

\[
\|(h+k)/2\|_p^p+\|(h-k)/2\|_p^p
\le(\|h\|_p^p+\|k\|_p^p)/2.
\]

The midpoints (h_n+φ)/2 converge weakly to φ. Lower semicontinuity and the triangle inequality show their norms converge to one. The displayed inequality then gives ||h_n−φ||p→0. This proves strong convergence of the original Lp-normalized extremizing sequence, after one subsequence and the frozen plus-sign modulations. It is not just strong L² convergence.

The sign is worth fixing explicitly: T(U_a h)(x)=Th(x−a). A peak at a is centered at zero by U_{−a}. The extracted profile is subtracted in the original frame as U_aφ. Thus the frozen modulation is indeed exp(+2πi a·ξ), and the later approximation in the original frame is U_aφ. The original index choices were strictly increasing; relabeling them n_k and the corresponding parameters a_k yields exactly the frozen sequential assertion.

## 6. Attainment and the entire stability statement

Because C is finite and positive, its definition gives a unit-norm sequence with output norms tending to C. The sequential result just proved provides a unit-norm extremizer. Thus the set M of all normalized extremizers is nonempty.

For every a, U_a is an isometry of Lp(μ), and T(U_a g) is an output translate of Tg. Hence U_aM=M (apply also U_{−a} for equality of sets). Therefore

\[
\inf_{g\in M}\|U_a f-g\|_p=\inf_{g\in M}\|f-g\|_p.
\]

If the claimed stability failed, there would be ε₀>0 such that for every δ>0 a unit-norm f has ||Tf||p≥(1−δ)C and distance at least ε₀ from M. Choose δ=1/n. The resulting f_n is extremizing, since the operator norm also gives ||Tf_n||p≤C. Its compactness subsequence satisfies U_{−a_k}f_{n_k}→φ∈M. The elements g_k=U_{a_k}φ belong to the ENTIRE set M and satisfy

\[
\|f_{n_k}-g_k\|_p=\|U_{-a_k}f_{n_k}-\phi\|_p\longrightarrow0,
\]

contradicting the distance lower bound. This proves the required strict distance <ε for some δ(Σ,p,ε)>0 for each ε>0. The argument is qualitative and gives neither a rate nor uniformity over surfaces, exactly as frozen.

## 7. Disposition of possible objections and review limits

The objections that would invalidate several superficially similar arguments do not invalidate this one. The L² extraction does not treat f_n as Hilbert-normalized extremizers. Lp membership is obtained from the original sequence, not from a nonexistent uniform Lp residual estimate. Brezis–Lieb is used only at fixed finite J with established bounded outputs and pointwise convergence. The uniform-in-J output bound comes from its nonnegative q₀ splitting, and the interpolation argument uses a genuinely available q₀<p. Countable extraction is made compatible by a single increasing diagonal subsequence. The local weighted mass inequality is proved with bounded measurable tests, and all equality deficits are nonnegative and integrable. Complex cancellation does not defeat the strict plus/minus inequality or injectivity. Boundary and disconnectedness do not defeat the chart estimate or output analytic continuation. The final modulus is qualitative and is taken relative to all normalized extremizers; no classification is needed.

I found no invalid deduction or missing essential application in the immutable text. The details above unpack its stated arguments; they do not change its hypotheses, replace a lemma, or supply a different restricted theorem.

All 29 canonical blobs were freshly acquired and authenticated against the complete stipulated tree. All 27 non-PDF canonical texts, including both actual wrappers, every included section, and companions, were semantically read. The compiled PDFs were authenticated but not rendered; the operative TeX was read instead. Actual selected primary proofs and the authorized original-history spans were read before this extended review was drafted. Private records give exact URLs, versions, byte extents, truncation recovery, and unattempted transitive reading. No claim of all-literature or all-transitive clearance is made. Those limits leave no unpaid dependency in the new deduction: the full source operation A is stipulated true and its applicability was checked; the compactness, splitting, square-mass, analytic, convexity, and stability steps needed beyond it are derived above.
