# Independent ordinary proof and complete prior bridge: 322479

This is an ordinary mathematical review by the assigned Sol reviewer, with no mathematical program, experiment, CAS or formal checker. The author's certificate is independently verified below. Its validity does not qualify it for discovery credit.

## Exact scope and graph

The frozen raw JSONL and decoded literal state the universal unique-nontrivial-fixed-point iff with denominator sqrt(n1+...+n_(ell-1)). In 1111.0531v2, §1.2 (1.7), a=1-delta and b=beta, with a,b in (0,1); §5 (5.1) displays the node update
F_i(x)=1-(1-a x_i) product_(j adjacent i)(1-b x_j).
The first line of (5.1) has a missing complement/sign inconsistency, and earlier time-indexed derivations are inconsistent. The explicit last line, (1.7), (5.2), and the later paper's displayed map agree. The review concerns that explicitly displayed deterministic probability map, not the exact finite-state stochastic SIS chain or an implicitly time-indexed alternative.

Conjecture 5.2, p15, describes children per vertex, not total nodes per level. Take levels {v1},{v2},{v3},{v4}, root v1, edges {v1,v2},{v2,v3},{v3,v4}, and n1=n2=n3=1. Every nonleaf has exactly its prescribed one child; there are exactly four vertices. These are positive integral branching numbers. No global ni>=2 condition is present in the inspected setup/conjecture. The original paper explicitly discusses n=1 in Appendix A; restrictions n>=2 in particular two-level estimates are not standing restrictions on Conjecture 5.2. The later paper uses positive integers in its proof and has no extra branching restriction in §4.1. A sentence concerning n2>=2 in its three-level proof addresses one case, not a universal premise.

For this tree level coordinates ARE all vertex coordinates. Neither common-level convergence nor graph-reflection symmetry is needed. Rooting at an endpoint is allowed by the printed construction: no maximum-degree or graph-center requirement is imposed on the root. The terminology hub does not add such a condition. Thus a proof on all four coordinates proves absence of arbitrary node fixed points as well as of level-synchronized fixed points.

## Exact certificate

Let a=1/2 and b=3/10. Both lie strictly between zero and one. On [0,1]^4 the coordinates are
F1=1-(1-x1/2)(1-3x2/10),
F2=1-(1-x2/2)(1-3x1/10)(1-3x3/10),
F3=1-(1-x3/2)(1-3x2/10)(1-3x4/10),
F4=1-(1-x4/2)(1-3x3/10).
Every factor belongs to [0,1], so F maps the cube into itself, and F(0)=0.

For u,v in [0,1], 1-(1-u)(1-v)=u+v-uv<=u+v. Put q=1-(1-u)(1-v), which belongs to [0,1]; applying the same inequality to q,w proves the three-factor bound. Applying these bounds gives
F1<=x1/2+3x2/10,
F2<=x2/2+3x1/10+3x3/10,
F3<=x3/2+3x2/10+3x4/10,
F4<=x4/2+3x3/10.
Let B=(1/2)I+(3/10)A(P4). For w=(3,5,5,3), the four coordinates of Bw are respectively 3,49/10,49/10,3: endpoints 3/2+15/10=3; interiors 5/2+24/10=49/10. B is symmetric.

At ANY cube fixed point x, summing the four majorants with weights w gives
3x1+5x2+5x3+3x4 <= 3x1+(49/10)x2+(49/10)x3+3x4.
Consequently (x2+x3)/10<=0. Nonnegativity implies x2=x3=0. The endpoint exact fixed equations reduce to x1=x1/2 and x4=x4/2, so both endpoints are zero. Hence zero is the ONLY fixed point in the entire cube.

The claimed threshold is exceeded: 3/10>1/(2 sqrt(3)). Both quantities are positive. Squaring reduces the comparison to 9/100>1/12, equivalently 108>100. A universal assertion that the right-hand inequality implies existence of exactly one nonzero fixed point is false on this witness: there are none. This negates the entire proposed iff, not just a symmetry restriction or a uniqueness subclaim. No claim of minimality or of a repaired general threshold is required.

## Later asserted theorem and elimination failure

2212.05733v2 §4.1 p18 displays the k-coordinate map with a parent factor and n_m child factors at each interior level, exactly as above for k=4 and n_m=1. Theorem 4.1 II(a) prints the same sum-under-square-root threshold and asserts existence of a unique nontrivial fixed point. All parameters, boundary coordinates and neighbor multiplicities agree here. Its mistaken total-node count n1+...+n_(k-1)+1 on p4 also happens to equal four in this case. It cannot remove the contradiction. Thus the certificate contradicts the actual displayed v2 theorem; invoking that theorem to reject the certificate would be circular.

In §4.2 p19 (4.6), substituting d_k=b d_(k-1)/(1-a+ab d_(k-1)) into the preceding equation leaves d_(k-1) on both sides and d_(k-2) as an independent variable. This is an implicit equation, not an explicit composition in d_(k-2). Its solution branch, existence, uniqueness and derivatives need separate justification. Lemma 4.3 then applies composition-concavity as if that implicit resolution had already been paid. Similar functional shape does not justify adding branching numbers in the threshold.

A local diagnostic makes the missing dependency explicit, without any computation program. At zero put c=b/(1-a)=3/5. Linearized tail fixed equations give d4=c d3, (1-c^2)d3=c d2, hence the tail slope d3/d2=15/16. The next relation is d2=c d1+c d3, giving d2/d1=48/35. The first relation d1=c d2 therefore has slope product 144/175<1, while replacing the chain by the claimed three-level sum would use 3c^2=27/25>1. These are derivatives of the fixed equations at zero, not an assumption of globally linear dynamics. The weighted proof above supplies the global conclusion independently.

## Complete applicable primary-to-target routine bridge

A genuinely distinct work, Azizan Ruhi, Ahn and Hassibi, arXiv:1609.09565v1 (30 September 2016), was acquired and read directly. This is not an alternate or expanded delivery of denied WDWF2003; no body of the denied work was recovered or used. The chosen work proves its own sufficient bound in §2.2.1, p4, equations (2.9)-(2.12) and the immediately following conclusion. Its graph is a connected finite network with adjacency A (p2), its domain is [0,1]^n (p3), and its displayed nonlinear map (2.6) is
Phi_i(x)=(1-delta)x_i+(1-(1-delta)x_i)(1-product_(j in N_i)(1-beta x_j)).
With delta=1-a and beta=b this equals 1-(1-a x_i)product(1-b x_j), EXACTLY the target. This is the paper's nonlinear mean-field model, not its separately treated exact Markov chain and not its later immune-admitting variant.

The actual printed proof bounds Phi(x) <= ((1-delta)I+beta A)x by dropping a multiplier <=1 and using the product union bound. Iterating this nonnegative matrix bound gives Phi^t(x)<=B^t x. The source concludes convergence to zero and uniqueness of its fixed point when beta lambda_max(A)/delta<1. No other theorem or omitted appendix proof is needed for this subcritical assertion: all its proof is on p4.

For P4 let phi=(1+sqrt(5))/2 and v=(1,phi,phi,1). It is positive and phi^2=phi+1, so Av=phi v coordinate by coordinate. To verify it is the largest adjacency eigenvalue without assuming a formula for path spectra: for any eigenvector z with eigenvalue mu choose i maximizing |z_i|/v_i. Then |mu||z_i|<=sum_(j~i)|z_j|<=phi v_i |z_i|/v_i=phi |z_i|, hence |mu|<=phi. As phi is itself an eigenvalue, lambda_max(A)=phi (A is real symmetric). Moreover sqrt(5)<7/3 since 5<49/9; thus phi<5/3 and beta lambda_max(A)/delta=(3/5)phi<1. All hypotheses of the source's proved extinction assertion hold. Alternatively its comparison bound immediately yields Phi^t(x)<=C(1/2+3phi/10)^t v for C=max_i x_i/v_i, showing global extinction directly with a positive weight vector. A nonzero fixed point cannot converge to zero.

Combining that established general-network result with the exact threshold comparison above is a COMPLETE routine adaptation refuting the target sum threshold. It even gives more than the rational certificate, namely extinction for every initial cube point. Finding rational weights avoids radicals in a future certificate but changes no mathematical endpoint or substantive content. No result from WDWF2003 is attributed as proved, and its heuristic description in the original paper was not used as correctness clearance.

## Other variants and limits

For all paths of ell>=6, a=1/2,b=1/4, the union bound summed over vertices forces both endpoints zero at a fixed point, because each interior coordinate is counted twice and endpoints once. The exact endpoint equations then force neighboring coordinates zero and induction propagates. sqrt(ell-1)>2 makes the printed threshold exceeded. This is the same mechanism/family and is covered by the same general-network comparison argument, not extra credit. The golden-ratio version and rational P4 proof are also one family.

The strongest significance case is that an interior-parameter, all-coordinate refutation exposes a genuine conflict in the later explicit theorem, rather than fixing a boundary convention. The strongest contrary case now has an actual applicable primary proof, identical model, verified graph/parameter substitutions and exact spectral inequality: it is a routine consequence of established general extinction. This outweighs the significance case under the campaign's explicit exclusion rule. It does not prove that an explicit refutation of Conjecture 5.2 was published previously, nor does it certify worldwide priority. Source-final/correction questions are separately unresolved and do not undo this ordinary bridge.
