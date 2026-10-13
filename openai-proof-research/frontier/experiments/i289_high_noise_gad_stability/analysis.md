# I289 — rank-unrestricted unital GAD stability at high noise

2026-10-13. **Proof verdict: the requested all-n theorem is proved, subject to ordinary independent review. Contribution assessment: a rank-unrestricted completion in the assigned parameter region; substantiality and priority require separate review. No acceptance claim.** Twelve accepted findings toward twenty remain unchanged.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Entropy uses natural logarithms and trace norm is unhalved. The proof is for pure inputs of arbitrary tensor length, with no phase, Schmidt-rank, support, complexity or small-distance hypothesis.

## 1. Exact theorem and dependencies

Let $0<s\le1/3$, and let $A_s=A_{1-s^2,1/2}$ have Bloch multipliers $(s,s,s^2)$. Put

\[
 m_s=h((1+s)/2),\qquad
 D_s(\psi)=S(A_s^{\otimes n}(P_\psi))-nm_s,
\]

and let $M_n$ consist of products of the pure equatorial states $(|0\rangle+e^{i\theta}|1\rangle)/\sqrt2$.

**Theorem.** For every $s\in(0,1/3]$, every integer $n\ge1$, and every unit vector $\psi\in(\mathbb C^2)^{\otimes n}$,

\[
 \inf_{\phi\in M_n}\|P_\psi-P_\phi\|_1^2
 \le \frac{240+32/(1-s^2)}{s^2}\,D_s(\psi)
 \le \frac{276}{s^2}\,D_s(\psi).                 \tag{U-EB}
\]

Consequently $276/a^2$ works simultaneously for $s\in[a,b]\subset(0,1/3]$. There is no assertion of uniformity as $s\downarrow0$.

The pinned family-276 source gives the channel formula `eq:channel`, minimum-output value `eq:minimum-output-value`, partner theorem `cor:partner-additivity`, pure branch inequality `lem:partner-branch`/`eq:recursion`, thermal table `eq:thermal-table`, and unital specialization `cor:unital`. The actual wrapper and complete output, thermal, partners and special sections were read. Fresh immutable raw bytes match both the retained copies and the exact-path Git blobs. The branch inequality is used only to rederive the paid amplitude bound in §6; the productness argument uses an EB measurement recursion.

The only non-elementary additional inputs are strong subadditivity of von Neumann entropy and the older product-test soundness bound in Soleimanifar–Wright, [arXiv:2201.01824v1](https://arxiv.org/html/2201.01824v1), Theorem 15. Its complete §2.1 proof was read and checked. Shor, [arXiv:quant-ph/0201149v1](https://arxiv.org/html/quant-ph/0201149v1), Theorem 1, equations (5), (7)–(14), supplies the classical EB entropy argument; its representation and full proof were read. We explicitly derive its required specialization below, including mixed preparation states.

The parent shared the same swap-test bridge after this author reported a candidate bridge. The subsequent authorized supplement `frontier/iterations/i289-parent-swap-test-bridge.md` was read completely. We adopt and credit its pairwise derivation in §4, alongside the author's covariance derivation. This is shared mathematical input, not an independent review of this final theorem. No exclusive authorship or independent discovery claim is made.

## 2. An explicit rank-one measure-and-prepare channel

For $a\in\{X,Y,Z\}$, let $P_{a,\pm}=(I\pm a)/2$ and

\[
 E_a(\rho)=\sum_{\pm}\operatorname{Tr}(P_{a,\pm}\rho)P_{a,\pm},
 \qquad R(\rho)=\operatorname{Tr}(\rho)I/2.
\]

These are, respectively, complete dephasing in the indicated Pauli basis and complete replacement by $I/2$. Directly on the Pauli basis,

\[
 A_s=sE_X+sE_Y+s^2E_Z+r_sR,\qquad r_s=1-2s-s^2.       \tag{2.1}
\]

For the assigned interval, $r_s\ge2/9>0$, so this is a convex combination of CPTP EB channels. Specify the full representation by eight outcomes $(a,\pm)$, where $a=X,Y,Z,R$. The weights are $w_X=w_Y=s,w_Z=s^2,w_R=r_s$. For $a=X,Y,Z$, the POVM effect is $w_aP_{a,\pm}$ and the preparation is $P_{a,\pm}$. For $a=R$, the effect is $r_sP_{Z,\pm}$ and the preparation is $I/2$. Their effects sum to $I$, and every nonzero effect has rank one.

For a pure state on a first qubit and a tail, outcome $o$ has probability $p_o\ge0$ and a normalized pure tail vector $\chi_o$ whenever $p_o>0$. Completeness gives

\[
 \rho_B=\operatorname{Tr}_1P_\psi=\sum_o p_oP_{\chi_o}. \tag{2.2}
\]

If $p_o=0$, choose an arbitrary normalized tail vector and omit its zero contribution. This avoids division by zero. No orthogonality between the tail vectors is needed. The representation is a finite algebraic construction, not a numerical enumeration of trees.

## 3. Entropy recursion and its local impurity cost

Let $N$ be any finite-dimensional CPTP tail channel and write $T_o=N(P_{\chi_o})$, with root preparation state $\theta_o$. Form the classical extension

\[
 \Omega_{QBL}=\sum_o p_o\theta_o\otimes T_o\otimes|o\rangle\langle o|.
\]

Its $QB$ marginal is $(A_s\otimes N)(P_\psi)$, and its $Q$ marginal is $A_s(\rho_1)$. Strong subadditivity in the form

\[
 S(QB)\ge S(QBL)-S(QL)+S(Q)
\]

therefore gives

\[
 S((A_s\otimes N)(P_\psi))
 \ge S(A_s(\rho_1))+\sum_o p_oS(T_o).                \tag{3.1}
\]

Indeed the two classical-block entropies cancel the Shannon term and the preparation entropies, leaving exactly $\sum_op_oS(T_o)$. The preparations may be mixed: this includes the $R$ outcomes and requires no pure-preparation assumption.

For a qubit state $\rho=(I+\mathbf r\cdot\boldsymbol\sigma)/2$, let $u=|\mathbf r_{\rm out}|^2=s^2(r_x^2+r_y^2)+s^4r_z^2\le s^2$. Define $G(u)=h((1+\sqrt u)/2)$. Direct differentiation, continuously at $u=0$, gives

\[
 -G'(u)=\frac{\operatorname{atanh}\sqrt u}{2\sqrt u}\ge\frac12.
\]

Since $s^2-u=s^2(1-|\mathbf r|^2)+s^2(1-s^2)r_z^2$, integration yields

\[
 S(A_s(\rho))-m_s\ge2s^2\det\rho
       +\frac{s^2(1-s^2)}2r_z^2\ge2s^2\det\rho.     \tag{3.2}
\]

For pure inputs the maximum output length $s$ is attained at the equator, so $m_s$ is the single-use minimum. Mixed states also satisfy (3.2). Taking $N=A_s^{\otimes(n-1)}$ in (3.1) gives

\[
 D_s(\psi)\ge2s^2\det\rho_1+\sum_op_oD_s(\chi_o). \tag{3.3}
\]

Apply the same eight-outcome measurement at each successive qubit. Let $v$ range over nodes before a measurement, let $q_v$ be its probability, and let $\rho_{v,1}$ be the next-qubit marginal of the normalized pure state at that node. Iteration, with a scalar leaf entropy of zero, proves

\[
 D_s(\psi)\ge2s^2\sum_v q_v\det\rho_{v,1}.         \tag{3.4}
\]

All local costs are nonnegative. At the last qubit the conditional input is pure and its determinant is zero; its nonnegative latitude deficit may simply be dropped. The leaf probabilities sum to one. The factor $2s^2$ is constant at every depth, with no selected exponentially rare branch.

## 4. Paying a global two-copy product test with that same tree

Let $W_j$ swap the two copies of site $j$, let $\mathrm{Sym}_j=(I+W_j)/2$, and put

\[
 \Pi_n=\prod_{j=1}^n\mathrm{Sym}_j,\quad
 T_n(\psi)=\operatorname{Tr}(P_\psi^{\otimes2}\Pi_n),\quad
 F_n(\psi)=1-T_n(\psi).
\]

For zero sites set $T_0=1,F_0=0$. Put $H=\prod_{j\ge2}\mathrm{Sym}_j$ and $\rho=\rho_B$. Because $HW_B=H$ and the full swap fixes the two identical pure copies, the two terms in $\mathrm{Sym}_1$ have the same expectation. Hence

\[
 T_n(\psi)=\operatorname{Tr}(H\rho^{\otimes2}).      \tag{4.1}
\]

This identity requires purity of the full input; it does not require the tail marginal to be pure or product.

For **any** finite pure-state ensemble $\rho=\sum_ip_i\sigma_i$, the shared parent derivation gives the exact identity

\[
 \sum_ip_iT_{n-1}(\chi_i)-T_n(\psi)
 =\frac12\sum_{i,j}p_ip_j
   \operatorname{Tr}\bigl[H(\sigma_i-\sigma_j)^{\otimes2}\bigr]. \tag{4.2}
\]

Here $\sigma_i=P_{\chi_i}$. Since $\|H\|_\infty\le1$ and the unhalved pure-projector formula is
$\|\sigma_i-\sigma_j\|_1^2=4(1-\operatorname{Tr}\sigma_i\sigma_j)$,

\[
 \sum_ip_iT_{n-1}(\chi_i)-T_n(\psi)
 \le2(1-\operatorname{Tr}\rho^2)=4\det\rho_1.       \tag{4.3}
\]

No claim about the sign of (4.2) is needed. Equivalently,

\[
 F_n(\psi)\le\sum_ip_iF_{n-1}(\chi_i)+4\det\rho_1. \tag{4.4}
\]

**Independent covariance check.** Put $\Delta_i=\sigma_i-\rho$. Ensemble averaging cancels the linear terms, so the left side of (4.2) also equals $\sum_ip_i\operatorname{Tr}(H\Delta_i^{\otimes2})$. The tail support has dimension at most two because the removed site is a qubit; each $\Delta_i$ is traceless on that support. Thus $\|\Delta_i\|_1^2=2\operatorname{Tr}\Delta_i^2$, and the absolute-value bound is $2\sum_ip_i\operatorname{Tr}\Delta_i^2=2(1-\operatorname{Tr}\rho^2)$. This verifies the same coefficient. The pairwise proof does not need a support-rank observation, and is the version adopted here.

Use exactly the ensembles (2.2) at every node of §3. Since the terminal $F$ terms vanish, (4.4) and (3.4) imply

\[
 F_n(\psi)\le4\sum_vq_v\det\rho_{v,1}
            \le\frac2{s^2}D_s(\psi).              \tag{4.5}
\]

This is the new global test-to-entropy payment in the assembled proof. It concerns conditional marginals in a measurement tree. It never asserts the false lower bound by the sum of the original one-site determinants.

## 5. Older global soundness supplies arbitrary productness

Let

\[
 \epsilon(\psi)=1-\max_{\Phi\ \mathrm{pure\ product}}
                         |\langle\Phi,\psi\rangle|^2.
\]

Soleimanifar–Wright Theorem 15 states, for every number of parties and all finite local dimensions, $T_n(\psi)\le2/3+\omega^2/3$, where $\omega=1-\epsilon$. Its complete induction proof, including the Schmidt expansion and the nonnegative subtractions in equations (1)–(3), was checked. Consequently

\[
 F_n(\psi)\ge(1-\omega^2)/3\ge\epsilon(\psi)/3,
 \qquad\epsilon(\psi)\le\frac6{s^2}D_s(\psi).       \tag{5.1}
\]

This is an older soundness theorem, not an I289 contribution. It is global, so no local Taylor remainder or near-minimizer entry argument is missing. Pure-product maximization is over a compact finite-dimensional product of unit spheres for each $n$, merely to attain the maximum; no n-uniform estimate is inferred from compactness. For $n=1$, $\epsilon=F_1=0$.

## 6. The paid amplitude estimate, rederived from the actual GAD recursion

Let $q(x)=|\langle x|\psi\rangle|^2$, $u_n(x)=2^{-n}$, and

\[
 c_s=\frac{(1-s^2)s^2}{2}>0.
\]

We need exactly the I280 amplitude theorem, not its unresolved PH or TP. Here is its specialization and proof. For a computational-basis prefix $v$ of positive probability, let $p_v$ be the next-bit conditional probability. Family-276 `eq:recursion` iterates to

\[
 D_s(\psi)\ge\sum_vq(v)[e(p_v)-m_s],
 \quad e(p)=g((1-s^2)/4+(1-s^2)s^2(p-1/2)^2).
\]

The determinant-entropy function satisfies $g^{\prime}(a)=2\operatorname{atanh}\sqrt{1-4a}/\sqrt{1-4a}\ge2$, continuously at $a=1/4$. Thus $e(p)-m_s\ge2(1-s^2)s^2(p-1/2)^2$. The elementary inequality $\log r\le r-1$ gives $\mathrm{KL}(\mathrm{Bern}(p)\|\mathrm{Bern}(1/2))\le4(p-1/2)^2$. The classical chain rule now yields

\[
 D_s(\psi)\ge c_s\mathrm{KL}(q\|u_n).             \tag{6.1}
\]

Zero-probability prefixes are omitted; deterministic bits use the continuous endpoint formulas. Since $u_n$ is strictly positive, the KL is finite even when $q$ has zeros. This is a spent project result, included to make the proof dependencies explicit.

## 7. Global latitude rounding with no dimension loss

Choose a closest arbitrary pure product $\Phi=\bigotimes_j\phi_j$ as in §5 and let $p(x)=|\langle x|\Phi\rangle|^2$. Let $\widehat\Phi\in M_n$ have the same relative phase as each $\phi_j$ and equal local amplitudes. If a factor is at a pole, either relative phase may be chosen. The product phases exist even at zeros, and

\[
 |\langle\Phi,\widehat\Phi\rangle|
      =\sum_x\sqrt{p(x)u_n(x)}.
\]

Write $H^2(a,b)=\sum_x(\sqrt{a(x)}-\sqrt{b(x)})^2$. The triangle inequality for amplitudes and Jensen for the KL-affinity comparison give

\[
 H^2(p,q)\le2(1-|\langle\Phi,\psi\rangle|)
             =2(1-\sqrt{1-\epsilon})\le2\epsilon,
\]

\[
 H^2(q,u_n)\le\mathrm{KL}(q\|u_n)\le D_s/c_s.
\]

For the second inequality, if $a=\sum_x\sqrt{q(x)u_n(x)}$, then $a\ge e^{-\mathrm{KL}/2}$ by Jensen on the $q$-support, so $2(1-a)\le\mathrm{KL}$. The Euclidean squared triangle inequality therefore gives

\[
 H^2(p,u_n)\le4\epsilon+2D_s/c_s.                  \tag{7.1}
\]

The pure-projector distance identity and $1-a^2\le2(1-a)$ show

\[
 \|P_\Phi-P_{\widehat\Phi}\|_1^2
 \le4H^2(p,u_n)\le16\epsilon+8D_s/c_s.
\]

Finally, the squared trace-norm triangle inequality proves

\[
 \|P_\psi-P_{\widehat\Phi}\|_1^2
 \le2(4\epsilon)+2(16\epsilon+8D_s/c_s)
 =40\epsilon+16D_s/c_s.
\]

Substituting (5.1) and $c_s=(1-s^2)s^2/2$ proves (U-EB). This rounding uses full probability laws and Hellinger distance. It does not sum errors in n individual latitudes or compare output entropies by dimension-dependent continuity. ∎

## 8. Attempts, scope, and contribution collision

The first approach expanded the parent-supplied convex mixture $A_s=((1+s)/2)\mathcal D_s+((1-s)/2)C_s$. Its CPTP algebra is correct for $s\le1/3$; each tensor branch is EB and has the same additive minimum. Concavity alone gives an average of heterogeneous branch deficits, but no uniform stability estimate for those branches was initially available. Selecting the all-depolarizing branch costs $((1+s)/2)^n$. Partial output transposes were not assigned equal entropy. This route did not prove an entropy comparison.

The second approach used rank-one measure-and-prepare and Shor. Direct geometric-infidelity gluing appeared to require control of changing branch optimizers. The quadratic two-copy test eliminates that selection: its exact ensemble identity cancels linear errors and telescopes with the same conditional impurity costs as the entropy. No desired strong data-processing or tensorization estimate is assumed. One can also apply §§3–5 to the heterogeneous $\mathcal D_s/C_s$ tensor branches once this mechanism is available, but that is unnecessary for the target.

The explicit decomposition (2.1) is in fact valid for $0<s\le\sqrt2-1$; the same proof and unsimplified $K_s$ apply on that interval, including the endpoint $r_s=0$ after omitting the zero effects. This is a checked extension of the same theorem, not a second finding. The assigned $s\le1/3$ remains the main target. We do not claim a theorem for non-EB GAD or full unresolved U. The parent's proposed general interior EB GAD extension is recorded as shared context, not asserted as an additional completed I289 result here.

Uniformity at zero would be false even at $n=1$: for $\psi=|0\rangle$, the left side is $2$ and the deficit is $h((1+s^2)/2)-h((1+s)/2)=s^2/2+O(s^4)$. Thus any valid constants must diverge at least as $4/s^2$. No numerical scan is involved.

Closest collisions are **Shor's EB strong-additivity proof**, **Harrow–Montanaro product-test stability**, and **Soleimanifar–Wright's global soundness theorem**. They pay the entropy recursion and product-test-to-productness parts. Bae et al. is the closest inspected output-von-Neumann-entropy stability comparator, but is depolarizing-specific; we do not use its Taylor proof or transfer it through the non-CP same-s postmap excluded in I284. I280 pays the amplitude correction. I288's fixed-type core reduction has a different limitation: this proof has no dependence on any phase-rank parameter.

The precise connecting deduction in this assembly is (4.1)–(4.5), shared with the parent, followed by the dimension-independent latitude conversion (7.1). This establishes a genuine rank-unrestricted theorem in a parameter subregion, rather than a bounded-complexity corollary. Its ingredients and connecting calculation are economical and could be classified as a technical consequence of older work under a contribution review. No exact prior theorem giving this GAD bound was established in the bounded primary-source screen. Search absence establishes neither novelty nor worldwide priority. **Proof, substantiality, priority and acceptance remain separate judgments.**

## 9. Validation and boundaries

Validation is analytic: channel coefficients and completeness; the classical-extension entropy cancellation; the Bloch gap; both independent forms of the ensemble identity; same-tree telescoping; the global soundness theorem's exact overlap convention; the KL chain rule; and full-law latitude rounding. All constants are explicit. Positive-probability branches, zero outcomes, empty tails, one-site inputs, poles, arbitrary input zeros, $D_s=0$, and $s=1/3$ are handled above. At $D_s=0$, (5.1) forces productness and (6.1) forces uniform amplitudes, yielding an equatorial product exactly.

Only the five assigned I289 deliverables are written. No subagents, I287 reads, other live sibling reads, shared-index edits, staging, commits, publishing, numerical scans, or giant history replay are used. External full bodies are fetched only in memory for reading and hashing; none is retained in deliverables. Authentication records exact semantic read extents separately from whole-body hashes. Detached output SHA256s accompany the handoff.
