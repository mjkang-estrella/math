# I221 — early contribution screen for quantitative Coulomb maps

**Early assessment: SUPPORTS FURTHER VALIDATION, with a narrow contribution claim.** The possible result is a sharp quantitative transfer to the source's smooth, full-dimensional, five-component Coulomb/Riesz example, valid against every marginal-preserving Borel pair and attained in order by exact three-cycles. The powers themselves, oscillatory mass splitting, transport/interface interpolation, and cyclic approximation are not new mechanisms. The especially close comparison is Carioni–Del Grande–Iglesias–Schönberger, arXiv:2609.05062v1, Examples 2.8 and 4.6, rather than only De Pascale–Louet–Santambrogio, arXiv:1407.7022v3.

This is not a proof gate, final contribution gate, nomination, or acceptance decision. The proposed bounds remain unproved hypotheses here. No I220 live output was read. The nine accepted findings and pinned upstream results are premises, not subjects of this review. A completed statement and proof must receive a fresh independent contribution assessment; this report cannot substitute for it.

## 1. Actual pinned interface

All nine manuscript files read in place under `frontier/sources/i217_quantitative_coulomb_monge/` match bytes retrieved from their raw GitHub paths at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The authentication JSON records both hashes and URLs. The source is *A counterexample to the Monge ansatz for the three-marginal Coulomb cost*, not merely the family-373 catalogue summary.

The relevant accepted interfaces are:

- `local.tex`, Lemma `lem:local`: fixed positive outer coordinate $y$, common central potential, and a positive definite $(x,z)$-Hessian after subtracting the prescribed potentials; the minimizing maps $X_k,Z_k$ are separately local diffeomorphisms.
- `certificate.tex`, Proposition `prop:certificate` and Lemma `lem:common-ball`: a common certificate on five disjoint component balls, contact triples $(x,Y_k(x),W_k(x))$ and their permutations, $Y_k=X_k^{-1}$, $W_k=Z_k\circ Y_k$, and four diffeomorphisms on one ball $B$.
- `proof.tex`, equation `eq:mu`: $\nu=g^2dx$, with a freely chosen nonnegative normalized $g\in C_c^\infty(B)$, and $\mu=\nu/3+\sum_{H\in\{Y_1,W_1,Y_2,W_2\}}H_\#\nu/6$. The optimal value is $3\int u\,d\mu$.
- `splitting.tex`, Lemma `lem:splitting`: pointwise branch selection fails by an exact factor-two image-mass deficit, including when other components also supply incoming mass.
- `infima.tex`, Proposition `prop:equal-infima`: an exact-marginal Borel cell construction already gives cost error at most $6\delta/\eta^2$, where $\eta$ is component separation. It does not claim BV/fractional control or a cyclic relation. Its transport lemma explicitly uses conditional distribution functions and inverse quantiles.
- `riesz.tex`, Theorem `thm:riesz`: for every fixed $d\ge2,s>0$, the same construction works for $c_s=\sum_{i<j}|x_i-x_j|^{-s}$; constants and the density may depend on $d,s$. Its existing Borel error is $6s\delta\eta^{-s-1}$.

Thus choosing a product bump positive on an interior cube is an allowed specialization of the source family. It is an additional choice that must be stated. The source does not specify one universal numerical bump, or already prove the proposed complexity laws for every permissible $g$.

## 2. Closest prior results and what they settle

The detailed bibliography and reading limits are in `frontier/sources/i221_coulomb_contribution_screen/literature.md`.

**The decisive comparison.** [Carioni et al., v1](https://arxiv.org/abs/2609.05062v1), Examples 2.8/4.6, treats uniform mass on a line segment sent to two parallel segments under squared distance, with fractional energy of order $t$, power $p>1$, $tp<1$. It uses exact-image alternating cell maps, obtains displacement cost of order $N^{-2}$ and fractional energy of order $N^{tp}$, and proves penalized excess of order $\varepsilon^{2/(2+tp)}$. Its lower proof uses branchwise monotone rearrangement, a primitive of the phase indicator, and interpolation. These are not merely qualitative relaxation results.

The implication for this screen is an elementary inference from that comparison: the proposed fractional constrained law has the same scaling content. If $D(S)\asymp S^{-q}$, minimizing $D(S)+\varepsilon S$ gives order $\varepsilon^{q/(q+1)}$; $q=2/(tp)$ yields precisely $2/(2+tp)$. Conversely a penalized lower bound can be optimized in $\varepsilon$ to obtain the constrained lower bound; the explicit recovery maps provide the other direction in that example. Changing from penalized to constrained notation is not a contribution. The paper's stated $p>1$ framework should not silently be cited for $p=1$.

**The requested 2014 comparison.** [De Pascale–Louet–Santambrogio, v3](https://arxiv.org/abs/1407.7022v3), Theorem 1.1, assumes Lipschitz polar domains and Hölder densities bounded above and below by positive constants. It gives exact-image Lipschitz density. Theorem 1.2 studies a quarter-disk-to-annular-sector geometry and Dirichlet penalization, with leading excess $(K/3)\varepsilon|\log\varepsilon|$. The optimal unregularized maps exist there but have infinite Dirichlet energy. Their setting therefore does not imply a vanishing first-order-Sobolev gap for the disconnected five-component example. It already establishes that exact marginal constraints, regularity penalties and quantitative excess asymptotics belong together; that broad theme cannot be claimed anew.

**Other known mechanisms.** [Colombo–Di Marino](https://cvgmt.sns.it/media/doc/paper/2127/MultiColDim.pdf), Theorems 1.1/1.4, already gives equality with the infimum over exact measure-preserving $N$-cycles for nonatomic identical marginals and continuous cyclic costs, including Coulomb. [Cinti–Otto](https://arxiv.org/abs/1509.01189v1), Propositions 1.1 and 1.3, and [Seis](https://arxiv.org/abs/1309.0556v1), Lemma 2, place transport/negative-norm versus interface estimates within established pattern-formation and mixing theory. They do not literally state this weighted branch-domination Coulomb bound. They do preclude claiming the interpolation principle or the competition between a quadratic defect and an interface cost as a new finding.

[Bindini–De Pascale](https://doi.org/10.5802/jep.59), Proposition 3.7, constructs exact-marginal absolutely continuous plans with controlled square-root kinetic energy and converging Coulomb cost. This regularizes plans, not deterministic maps. [De Pascale](https://arxiv.org/abs/1503.07063v2) concerns Coulomb approximation and duality, not the asserted map-complexity powers. Neither a wavefunction gradient nor a plan-density gradient can be substituted for $|DT_i|$.

## 3. What a substantive combined theorem would have to say

Fix $d\ge2,s>0$. Make one fixed permitted choice of $g$, for example a normalized product of nonnegative smooth bumps positive on a cube $\Omega\Subset B$, flat at its boundary. Put $D=\Omega\cup Y_1(\Omega)\cup W_1(\Omega)\cup Y_2(\Omega)\cup W_2(\Omega)$. Define

$$
\Delta(T_2,T_3)=\int c_s(x,T_2(x),T_3(x))\,d\mu-E_s(\mu).
$$

For illustration of the required quantifiers, define unweighted component-domain complexities

$$
V_D=|DT_2|(D)+|DT_3|(D),\qquad
S_D=[T_2]_{W^{t,p}(D)}^p+[T_3]_{W^{t,p}(D)}^p,
$$

where the second seminorm uses the full double integral on $D\times D$. Sum-of-component seminorms, central-domain seminorms and a whole-space extension are different conventions and must be identified and related, not interchanged. Bounded values and positive component separation make the cross-component terms bounded; whole-space extensions require an explicit trace/boundary argument.

The meaningful statement is: for all Borel pairs preserving $\mu$, finite relevant complexity implies

$$
\Delta\ge c(1+V_D)^{-2},\qquad
\Delta\ge c_{t,p}(1+S_D)^{-2/(tp)}\quad(0<t<1, 1\le p<\infty, tp<1),
$$

and there exist Borel $T_n$ with

$$
(T_n)_\#\mu=\mu,\quad T_n^3=\mathrm{Id}\ \mu\text{-a.e.},\quad
\Delta(T_n,T_n^2)\le Cn^{-2},\quad
V_D(T_n,T_n^2)\le Cn,\quad S_D(T_n,T_n^2)\le C_{t,p}n^{tp}.
$$

These assertions would yield matching two-sided orders for the constrained infima at all sufficiently large budgets. They do not assert that every map saturates a power, a sharp leading constant, or a unique minimizing pattern. Constants must depend only on fixed geometric/density data and, as appropriate, $d,s,t,p$, never on the competitor or $n$. No uniform claim as $tp\uparrow1$, $s\to0$, or across all source bumps is licensed.

An equivalent penalty formulation would have exponents $2/3$ for $\Delta+\varepsilon V_D$ and $2/(2+tp)$ for $\Delta+\varepsilon S_D$. Those are consequences of the combined bounds, not extra independent findings.

## 4. Source-specific obligations that remain mathematically nontrivial

1. **Uniform coercivity, not just equality classification.** For $R=c_s-\sum_i u(x_i)$, prove a uniform quadratic distance bound to the appropriate branch on every permitted component pattern, and a uniform positive bound on the wrong patterns. Use compact supports, Hessian coercivity in the actual minimizing variables, and bounded derivatives of inverse branch maps. The source's zero-set description alone is insufficient. Both orientations of each branch and repeated-component/singular triples must be covered.

2. **All competitors, not preselected near-branch maps.** On the central domain put $S_j=\{x:T_2(x)\in H_j(\overline\Omega)\}$, $F_j=H_j^{-1}\circ T_2$, and let $S_0$ be the central-target phase. Exact preservation gives $(F_j)_\#(\nu|_{S_j})\le\nu/2$. It is domination, not equality; incoming mass from outer source components cannot be dropped. If $\nu$S_0$\le1/2$, one of four outer phases has mass at least $1/8$. Otherwise the bad-pattern gap must already control the defect. Null-set choices and the domain of each inverse need to be explicit.

3. **Interpolation with the correct measure.** The natural estimate to justify is a fixed phase-mass discrepancy bounded by $C r(1+V)+C r^{-1}\Delta^{1/2}$, or by $C r^{tp}(1+S)+C r^{-1}\Delta^{1/2}$. The second uses the fractional perimeter of an indicator, controlled by separation of target components and the $p$-power map seminorm. Show the extension/smoothing errors at $\partial\Omega$ and use bounded density without pretending that the flat bump has a positive global lower bound. The resulting powers are classical scale optimization, once the Coulomb coercivity and branch discrepancy are established.

4. **Exact three-cycle, with all five components.** Verify the conditional-CDF half-cell maps and inverses at zero-density endpoints, the coefficients $1/3,1/6$, and the piecewise definition $v\mapsto Y_k(F_k(v))\mapsto W_k(F_k(v))\mapsto v$. Check $T_n^2$, as well as $T_n$, throughout the two outer pairs. A construction on the central component alone does not preserve the required marginal.

5. **Why the cost improves to second order.** Uniform $O(n^{-1})$ latent displacement only gives first-order cost control without an additional argument. Apply Taylor expansion to the calibrated residual, whose full gradient vanishes at contact, on a compact collision-free neighborhood. Subtracting the potential is justified only after the exact marginal identities. This is the real upgrade over the source's $O(\delta)$ oscillation estimate, though stationary quadratic error is itself standard calculus.

6. **Actual regularity, including boundaries.** One-dimensional monotonicity may bound total variation even when inverse-CDF derivatives blow up. Prove the corresponding variation bounds for the product-domain construction, its smooth branch compositions, each cell reset, and $T_n^2$. Count traces on the support boundaries and justify any global bounded extension. A general multivariate conditional CDF is not automatically BV. For bounded BV maps, the translation estimate $\int|f(x+h)-f(x)|^pdx\le C\min(1,|h|(1+V))$, followed by integration in $h$, already gives $S\lesssim(1+V)^{tp}$ for $tp<1$. Thus the fractional upper estimate is largely a corollary of a correct BV recovery construction, not another new construction.

## 5. Integer-Sobolev and endpoint claims

For a product bump positive throughout connected $\Omega$, the anticipated first-order obstruction is topological. A continuous map into the separated support has one component label on $\Omega$. For $W^{1,1}_{\mathrm{loc}}$, composing with smooth component-label cutoffs should give a Sobolev function with zero gradient and hence the same constancy. The central mass is $1/3$, but every outer target capacity is $1/6$; preservation forces the label to be central. A uniform repeated-component residual gap would then yield an absolute cost gap. This requires the stated positivity/connectivity and residual bound, and is an elementary companion consequence, not the main contribution.

The proposed jump recovery maps do not justify any claim for $tp\ge1$. A nonzero jump across a regular hypersurface has divergent fractional energy there. Exclusion of every other possible competitor at that threshold is a separate assertion and must be proved if included. No claim about smooth near-optimal exact-marginal maps belongs in the proposed theorem.

## 6. Contribution boundary and final-assessment conditions

The potentially substantive object is **one combined theorem**: robust branch coercivity plus a sharp complexity law for actual smooth Coulomb/Riesz marginals, universally over preserving pairs, with optimal orders already attained in the more restrictive class of exact three-cycles. This would quantify the pinned nonattainment theorem in a way its qualitative approximation does not.

The most serious novelty objection is that it may ultimately be a routine nonlinear, full-dimensional realization of Carioni et al.'s splitting example. A final reviewer must compare the completed proof against Example 4.6 and its underlying interpolation references, not merely compare abstracts or titles. They must decide whether the simultaneous all-pairs lower bound, endpoint-degenerate smooth density, nonlinear calibration, and exact cyclic recovery require a substantive transfer theorem. If these reduce to an immediate existing general result or straightforward conjugation with controlled norms, the appropriate final classification is TECHNICAL/KNOWN. If only one inequality survives, or complexity is measured only on a convenience subset without a matching admissible recovery, reconsider the claimed contribution.

This screen supports doing that validation; it does not establish worldwide novelty. The $p=1$ endpoint, all $d,s$ specialization, and penalty reparameterizations should not be counted as separate substantial findings. Search misses supply no evidence of priority. The final theorem must cite its close predecessors explicitly and be independently assessed in its completed form.

## 7. Reading and conduct limits

The authentication JSON supplies detached SHA-256 input records. The literature file supplies exact excerpt scopes and source-copy hashes. Existing source copies were read in place; new copies are mathematical text extracts of only the recorded PDF pages, all fully read. No full-paper reading is claimed for an excerpt, and no figure/layout inspection is claimed. The I217 briefs and partial records were read as supplied in the user message, not as a fresh read of possibly changing research files. Only its source directory was read on disk. No I214/I220 live research, prior experiments, historical replay, or acceptance ledgers were read. Filename discovery included unrelated paths; their contents were not inspected. No subordinate agents, research code, tests, experiments, scans, snapshots, seals, shared edits, staging, commits, or publication were performed. Retrieval/extraction/hash bookkeeping were the only scripts used.
