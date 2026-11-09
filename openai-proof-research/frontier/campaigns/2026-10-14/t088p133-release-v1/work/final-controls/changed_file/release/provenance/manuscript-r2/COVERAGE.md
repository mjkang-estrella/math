# Coverage and limits

The complete mathematical draft retains the exact frozen theorem, including every nonsimple, repeated-Gale, zero and boundary case. It neither weakens to generic polytopes nor extends to >=7 facets or dimensions 5-8.

| Obligation | Manuscript coverage |
|---|---|
| Facet positivity, distinct actual normals, spanning and balance | Section 2; divergence and compactness; Section 4 nonzero-middle exclusion |
| Projection/zonotope factors | Section 2, Cauchy endpoint counting and extrusion induction |
| Mixed-volume hypotheses, trial negative supports | Section 2; precise inequality and first variation; exact section maximum |
| Attainment, interior maximizing level | Exact maximum lemma and Proposition A; no boundary-vanishing assumption |
| Complementary determinants, Euclidean simplex volume, coarea, Gamma/factorials | Section 3, every normalization explicitly derived |
| Centering, scaling, asymmetric Laplace signs | Section 4; coefficients centered once; density evaluated at minus W |
| Log-concavity, conditioning, survival integration and boundary terms | Section 5; usable Prekopa hypotheses and direct HNBUE-Laplace derivation |
| Universal two-bracket algebra, positivity and one-sided cases | Proposition B; direct cleared expansion, Cauchy-Schwarz and strictness |
| Partial fractions, alternating signs and exact quotient identity | Section 7; signed bilateral transforms and polynomial divisibility |
| Exact ten-pattern positivity and repeated-rate strictness | Section 7 and Appendix A, full 248-term sparse certificate and pure positive endpoint terms |
| Zeros and all-zero vector | Explicit reclassification and direct zero case; no density claim at b=0 |
| Minimum facet classification, affine invariance, simplex value | Section 8; polar classification, transformed area vectors and exact determinants |
| Method limits | Section 9; exact corner calculation, no geometric conclusion beyond scope |
| Attribution and PQ1-PQ5 | Section 1 and Appendix B; adopted joint-assembly assessment and bounded search/read limits |

## Integrated independently reviewed deterministic support

The parent adopted PASS_SCOPED_SUPPORT with no author repair. Exact reviewed coverage is 21 support declarations (3 definitions/18 theorems),20 implementation controls and15 independent semantic/type/use-site declarations. See Appendix C, unchanged `formal/implementation/COVERAGE.md` and `formal/review/review.md`; all 56 actual types and axiom reports are printed by the new relative wrapper. Only propext, Classical.choice and Quot.sound occur.

At Proposition B, equations (Sn), (mixture), (two-brackets) retain their original source labels `eq:Sn`, `eq:mixture`, `eq:two-brackets`. New Appendix C labels `eq:formal-hypotheses`, `eq:formal-bound`, `eq:formal-residuals` state the exact mapping. For ALL real alpha,beta,p,q,d,P,N with alpha,beta>0,sum2,0<p<1,q=1-p,d>=0,P,N>0,2dp²<P,2dq²<=N, `T088P133.rational_mixture_lt_one` proves (1+d)[p alpha/(alpha+P/p)+q beta/(beta+N/q)]<1. Non-strict wrapper, moment conversions, positive denominators and reduced p=0,p=1 expressions are included; d=0 is covered. `one_sided_lt_one` correctly needs no d>=0. The paper's Cauchy-Schwarz proof remains; Lean gives the equivalent residual/square decomposition.

The independent audit proves the original normalized bracket mapping and scalar-majorization composition with an EXPLICIT assumed scalar premise. It does not prove that premise for an expectation. The exact type contracts reject both reviewed added-premise mutations. Ten exact rational configurations and both historical eleven-case integrity suites passed; new wrapper reproduces the former two semantic checks and ten configurations, and new manuscript copy-only integrity controls are separate. No source repairs were made.

ENTIRELY UNFORMALIZED: actual-facet geometry and nonzero middle coefficients; mixed-volume attainment/coarea/Gamma-Dirichlet; distributions/log-concavity/HNBUE and expectation-to-mixture majorization; the ten-pattern certificate and probabilistic interpretation; continuity/zero/repeated-knot assembly and derivation of strict moments; simplex equality and every-six-facet geometric strictness; the full projection-body theorem. Algebra is support, not a substitute for these proofs.

Trusted Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 and eight auxiliaries. Only own source files rebuilt. No clean dependency-source rebuild or complete binary-cache authentication. Unchanged historical replay requires its original project inputs; the new relative wrapper runs from supplied copies and explicit trusted dependencies without them. Historical pending text remains only in attributed unchanged originals. Full independent manuscript review and all parent acceptance/count/release decisions remain external. Count18/20 unchanged; publication stopped.
