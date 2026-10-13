# I319 — three-state tree capacity: obstruction checkpoint

Date: 2026-10-13. **Core bridge not achieved. No acceptance or count change.** Fourteen findings remain accepted toward twenty. This round investigates the new target under `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; it does not recount R009 as another result.

The requested exact weighted $L^2$-capacity criterion remains unproved, including its necessity direction for one fixed $0<\lambda<1$ on arbitrary bounded-degree trees. This round does not refute that criterion. It refutes the proposed saving on unrestricted symmetric posterior laws and isolates the precise extra inequality needed for positive tree-generated experiments.

## Paid results

The [complete analysis and proofs](../experiments/i319_three_state_tree_capacity/analysis.md) use $m=E|p_0+\omega p_1+\omega^2p_2|^2\in[0,1]$, half the posterior chi-squared information. They prove:

1. The candidate is electrical $L^2$ capacity with resistance $(1-\lambda_e^2)/R_w$, not a squared-flow capacity. On a ray, $C_2=R_\infty/(1-R_\infty)$ and $m_\infty=R_\infty$. Perfect edges have zero resistance. On a locally finite tree infinite capacity is equivalent to a wholly perfect root ray and gives $m_\infty=1$.
2. For **all locally finite deterministic trees** and all known independent $0<\lambda_e\le1$, the standard weighted linear estimator proves
   \[
   m_\infty\ge C_2/(1+C_2).
   \]
   Thus sufficiency is paid in full variable-edge generality. This is standard spectral/electrical reasoning; it does not count as the intended nonlinear bridge or a substantial new finding.
3. For two independent marginal complex posteriors $u,v$, setting $s=u\bar v+\bar u v$, $N=u+v+\bar u\bar v$, $a=E|u|^2,b=E|v|^2$, and $h_\mu=E\Re u^3,h_\nu=E\Re v^3$, the exact mixed identity is
   \[
   m(\mu\star\nu)=a+b-ab-2(h_\mu b+a h_\nu)
      +E[|N|^2s^2/(1+s)].
   \]
   Zero-normalizer contributions extend continuously with value zero.
4. Uniform support $|u|,|v|\le1/10$ gives the quadratic saving $m(\mu\star\nu)\le a+b-ab/2$. That support class fails product closure, explicitly at amplitude (7/34) after combining two aligned (1/10)-channel messages.

## Exact failure and the unpaid inequality

The balanced symmetric exclusion law $Q$, uniform on permutations of ((0,1/2,1/2)), has $m(Q)=1/4$ but $m(Q\star Q)=5/8>1/2$. The strictly interior orbit of ((1/9,4/9,4/9)) has information (1/9) and product information $23/99>2/9$. Diluting the first experiment with an observed uninformative mixture gives arbitrarily small input information, while preserving a **positive** product excess $\epsilon^2/8$. Hence symmetry, balance, strict interior support, and small expected information do not give the required saving.

These are negative observation channels, not demonstrated positive-broadcast tree laws. They refute the unrestricted route and any class closed under all symmetric degradations of revealing observations; they do not refute the target or the smallest class generated from revealing/uninformative laws by positive channels and products.

What remains unpaid on that generated class is a constant $c>0$ such that
\[
 E\frac{|N|^2s^2}{1+s}
 \le(1-c)ab+2(h_\mu b+a h_\nu).                        \tag{U}
\]
The analysis proves a conditional flow extraction from $U$. With $K=c/2$, $\kappa=K/(1+K)^2$, the change $g(m)=m+Km^2$ yields a weighted nonlinear recursion, and a conserved flow with $C_2\ge\kappa m_\infty$. Together with the paid lower bound this would prove the target, including perfect edges. **No such preserved-class inequality is established here.**

The mixed centered-log identities and the source radial inequality survive at individual vertices, but their positive cross term remains uncontrolled. `pos:moment-bounds` uses a common-law fixed-point identity to obtain its posterior moment region. `pos:correlation-bound` additionally uses regular/Poisson factorial moments. `loc:pair` smooths one input by a negative channel; `loc:gap` again uses a common law. None proves $U$ or a changed-potential converse on arbitrary trees. No identical-law recursion was imported.

## Source, contribution, and priority boundaries

The [reading and failure record](../experiments/i319_three_state_tree_capacity/reading-and-failures.md) identifies the actual primary passages and the complete four-state companions inspected. The [literature assessment](../sources/i319_three_state_tree_capacity/literature.md) checks Ising capacity, arbitrary-tree Potts contraction, robust reconstruction, critical geometries, homogeneous thresholds, and the general chi-squared non-subadditivity discussion. Neither a failed search nor an inaccessible 2026 branch-coupling paper is treated as evidence of novelty.

The source normalization and new algebra were independently derived and checked by formal polynomial cancellation and a few specified exact rational examples. No numerical scan, subagent, live sibling artifact read, Git operation, shared-index edit, new external body retention, or publication was performed. [Input authentication](../experiments/i319_three_state_tree_capacity/input-authentication.json) records source bytes against the complete pinned preprint tree, completed predecessor hashes, literature provenance, and the actual runtime; the requested Standard service setting is not independently visible to this agent.

Correctness is limited to the proved partials and the conditional implication. Contribution is a precise failure diagnosis, not a completed arbitrary-tree theorem. Worldwide priority is not established; global chi-squared non-subadditivity and the linear sufficiency mechanism are prior art. **Parent redirection:** concentrate further work on a positive-channel/product-preserved three-state constraint paying $U$, or on a different potential with a proved comparison. Repeating ray tests, regular/Poisson thresholds, or spherically symmetric capacity evaluations will not repair the missing necessity step.
