# Full nonnegative-bisectional uniformization: live author work

The exact prospective target is in scope-status.json. No proof or nomination is asserted. This is a new source338 screen, not an extension of the frozen 079 maximal target.

## Paid reductions and the actual unpaid step

Ni–Tam, arXiv:math/0304096v1, Theorem 4.2(i) and its proof (extracted lines 1778–1823), already split a simply connected complete manifold as N × M′, with N compact and M′ admitting a smooth strictly plurisubharmonic function of bounded gradient. Their Remark 4.1(c) credits the classification of N to Mok/Howard–Smyth–Wu. That compact classification primary body has NOT yet been read here. The theorem does not uniformize M′. Its polynomial-growth splitting in Theorem 0.5 is not a substitute.

Source338 only states uniformization under strict bisectional positivity everywhere. Its introduction explicitly excludes all growth/boundedness restrictions. Applying that theorem to M′ requires a new complete strictly-positive metric on each relevant factor; strict plurisubharmonicity of one function does not supply that metric's curvature.

## Route A: extend the localized flow, then split its null curvature

The source's initial-data construction can potentially start from Ni–Tam's strictly psh function: bounded gradient gives |psi| <= C(1+r); the complete L2 jet-interpolation argument needs strict Levi positivity on each fixed compact, not positive bisectional curvature separately. Its bundle-coefficient curvature only needs nonnegative bisectional curvature. These are observations about specific use sites, not a completed generalization of every source lemma.

A complete dependency check remains for source flow/disc/ellipsoid arguments. The localized flow theorem cannot simply be quoted with changed hypotheses. Even if it yields nonnegative bisectional curvature at positive times, the source's shrinking-chart proof uses strict curvature in two genuinely different places: positive Ricci at charts.tex 80–87 and the covector lower bound at 340–355. Ricci positivity alone does not imply the second bound.

A useful conditional quantitative step is available. If the generalized flow has the source scalar Harnack inequality, monotonicity h_t<=g, and the basepoint bound R(o,t)<=C, and if R>0, then for d=d_ht(x,o) choose t′=t+1+d². Integration along an almost-minimizing path gives R(x,t)<=C_T(1+d²)/t. The exit-distance index calculation in source charts.tex 116–158 then gives 1+l_L(t)>=(1+L)exp(-2 C_T sqrt(t)), hence completeness. The constant is uniform in exhaustion radius L, but not in T. This calculation is paid by the source once its exact preceding hypotheses have been established; it is not a new theorem nomination.

The substantive remaining tensor interface is to obtain a de Rham/holomorphic product of flat, compact symmetric, and strictly-positive factors from a complete, possibly unbounded-curvature positive-time flow. A bounded-curvature splitting/strong maximum theorem cannot be applied before its global bounds are proved. No such bound follows from the displayed quadratic distance estimate.

## Route B: add a strictly psh potential directly

This route has a concrete fourth-jet obstruction. Even on flat C with potential |z|², choose a local smooth potential psi=|z|²+A|z|⁴ near zero (A>0). It is strictly psh there. For g_epsilon=dd(|z|²+epsilon psi), the coefficient is 1+epsilon+4 epsilon A |z|². At zero its first derivatives vanish, whereas R_{z bar z z bar z}=-partial_z partial_bar_z g=-4 epsilon A<0. Thus adding a positive Hessian does not preserve even nonnegative holomorphic sectional curvature. This is a local obstruction to a proposed deformation rule, not a counterexample to the target. A globally constructed metric would have to control fourth derivatives and all mixed curvature directions, not just ensure completeness by g_epsilon>=g.

## Reading limits

All 13 source338 text blobs were fetched and matched to canonical tree Git blob identities. Download is not reading. Read introduction.tex in full; preliminaries.tex through the interpolation/canonical-section construction and heat-semigroup discussion as displayed, with the long combined output truncated later; reread explicit preliminaries lines420–470. Read flow.tex lines1–145 as displayed in two calls; charts.tex lines1–165 and330–360. Remaining source modules are unread except lexical navigation. Ni–Tam PDF extraction lines1–265 and1775–1840 read; Chau–Tam math/0504422v3 lines1–210 read. The latter retains bounded curvature and maximal growth or stronger curvature/decay assumptions. Search results on Mok factorization and newer flow results are navigation only, not body-verified dependencies.

Primary/source bodies remain ignored under private/. Source receipts are public identity records, not claims of full reading. No independent review has occurred.

## Primary factorization read and refined gap

Cao–Chen–Zhu, *Recent Developments on Hamilton's Ricci Flow*, Surveys in Differential Geometry XII (2008), Theorem 2.8, is a primary proof here, not merely a secondary attribution: its authors explicitly formulate and prove the noncompact factorization. Read PDF extraction lines650–1065, including the full displayed proof. The theorem assumes bounded and nonnegative bisectional curvature. It supplies complete strictly-positive factors, flat factors, and compact irreducible Hermitian-symmetric factors. Consequently the entire bounded-curvature case of our target is a paid composition with source338 and the compact Frankel theorem. It is not a candidate subclass.

Their algebra estimates the curvature reaction by c_K min(0,inf_vertical D²u), where c_K depends on the curvature bound. For a compact spacetime cylinder away from t=0, smoothness gives such a bound even for a globally unbounded flow. This suggests a local null-set propagation argument along a compact horizontal path, rather than a global maximum estimate with a uniform coefficient. However the precise strong maximum statement (their reference [7], Proposition 2) and holonomy/de Rham time dependence must still be read and justified. We do not infer an unrestricted factorization theorem just by replacing a global constant with local constants.

Read the remaining source flow.tex lines145–878 in three bounded calls. The largest-eigenvalue calculation discards -sum(lambda_i^-1 R_g(i,bar i,1,bar1)) using nonnegativity, not strict positivity. The localized limit, cofactor integration and nonlinear scalar comparison use the initial analytic-data package, g nonnegative bisectional, h<=g, scalar R_h>=0 and compact estimates. No new strict-bisectional use was found within these read passages. This materially localizes the next audit to preparation of the complete initial-data package and the disc/ellipsoid curvature-preservation chain. The latter modules have not yet been read in full. Nothing in this observation establishes complete positive-time metrics or full target closure.

## Local maximum-principle interface now derived

The actual Brendle–Schoen body (arXiv:0705.3963v1, lines1–240) shows its Proposition1 is local on an arbitrary Euclidean open set. The compact-base hypothesis in Proposition2 can be replaced, for a fixed parallel-transport path, by finitely many compact coordinate charts and local coefficient bounds. The explicit derivation is in local-null-propagation.md. This removes one alleged need for a GLOBAL curvature bound after existence/preservation has been supplied. It does not remove the other flow construction and factor-classification obligations. Also read source discs.tex1–160 and ellipsoids.tex280–522: the initial cotangent psh sandwich uses nonnegative bundle curvature, and the final scalar comparison is formulated through the localized-flow package. The uninspected middle disc/deformation chain remains a genuine reading/dependency limit.

## Author assembly checkpoint

The later nonnegative-flow-bridge.md and fixed-time-factorization.md assemble the full prospective target at author level. All three disc/deformation/ellipsoid modules have now been read in full, and the remaining source flow/preliminaries intervals were read in bounded calls. The earlier open-reading descriptions above are chronological, not current claims of an unresolved analytic input. Candidate.md gives the complete dependency order. Independent proof and contribution review remain pending; parent collaboration is not a gate.
