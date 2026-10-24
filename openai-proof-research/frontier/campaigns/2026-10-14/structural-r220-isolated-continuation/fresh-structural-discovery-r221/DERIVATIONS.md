# Structural discovery r221: working mathematical derivations

PREFREEZE exploration. No statement is frozen and no nominee or grade is asserted. Provenance: Codex / GPT-6 Astra / xhigh / default service tier, authorized header. Source345 and all operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are assumed true. The r220 wrapper is an isolation prefix only. All mathematical prose below is newly written in this root.

## Reading state before extended deductions

All eleven included mathematical sections, both operative figures, driver definitions and abstract, introduction applications, and bibliography have been read in complete bounded chunks. The source PDF was authenticated but not semantically read. The exact lean/docs/345.md endpoint failed HTTP 404. Exact byte extents are in private/reads.jsonl. Actual primary proof reading so far: HR 2012 v2 sections 3--7; BMW 2026 v2 sections 4--5; HW v4 section 1, subsection 2.4, Remark 4.14; CHO v3 sections 8.1--8.2; COS v1 sections 5--6. These are selected operative interfaces, not whole-paper coverage. Further primary dependency reading is recorded separately as it occurs. One guarded original-history scan had zero matches among eligible files; this is not clearance. Broad filename/substring exclusions omit useful originals, and opaque aliases can escape them.

## Exact paid mechanism

Work over F_2 on Lambda=H^1(S^1,S^n), n>=3. E is the integral of squared speed on period one; F=sqrt(E), and length ell<=F, with equality on constant-speed loops. Source ordinary-death gives D(g)>0 independent of a>0 and degree j so every global-null finite j-cycle in X_a={F<a} fills in X_(a+D), absolutely and relative to constants.

Its actual construction is not just an infinitude consequence. Put d=n-1, choose m=floor((j-2)/(2d)), q=2md, p=q-d, so r=j-q belongs to [2,2n-1]. A cochain T representing a power of omega vanishes below L=(p-C_H)/alpha-2; a cycle S representing Theta^m lies below l=(n+q+C_H)/alpha+2. Thus G=l-L=(2n-1+2C_H)/alpha+4. The native absolute cut D_T reduces degree by q and length by L-1. A fixed-degree filling W of D_Tx is joined with S. The absolute unit identity D_TS~[S^n] is corrected by V in degree n. The source interchange homology, joined W and V, and unit prism fill x below a+G+D_*+6, with D_*=max_(s<J)D_s. The radius may depend on the finite chains; the output length cost does not. Canonical coproducts cannot silently replace this native cut: HW Remark 4.14 explicitly rejects the corresponding Frobenius formula, while CHO uses another extension retaining constant components.

The finite-prime contradiction has additional costs: l_i, the finite root orders D_i, coarse polygon order N_0, root crossing rank B, support A, mean indices Delta_i, positive slope separation delta among {0,alpha,Delta_i/l_i}, and first activation thresholds. The source permits dependence on all of these. No uniform counting estimate is obtained by suppressing them. Its beta=0 case is handled via ordinary death in bounded degree, not division by zero. Quantitative rate, prime-length escape, entropy, or spatial density are not inferred.

## Feasibility calculation: uniformity over metrics

Fix a reference metric h and speed-comparison constants 0<u<=v<infinity. Consider all smooth g with u^2 h<=g<=v^2 h. This class is nonempty when u<=v; a constant multiple of h is an example. It need not have uniform curvature or injectivity radius, so an argument requiring those uniform bounds would be invalid.

The strongest actual HR proof provides more than a bare metric comparison. If mu_g is the common slope of critical levels of the powers, HR equation (19) gives

    (m-2)mu_g <= cr_g(Y Theta^m) <= (m+2)mu_g + cr_g(Y),
    degree(Y Theta^m)=2dm+degree(Y), 0<=degree(Y)<=3n-2.

There is a fixed finite generating set Q. Hence u mu_h<=mu_g<=v mu_h and cr_g(Y)<=v cr_h(Y). Setting alpha_g=2d/mu_g, one obtains a uniform resonance error from finitely many h-critical values, rather than propagating an error proportional to j. For high degrees a permissible error is

    max(7n-6, 4d + (2dv/(u mu_h))*max_Q cr_h(Y)).

The finitely many low nonzero groups can be absorbed using their h-critical values. The dual rank-one pairing supplies the same cohomological bound. This is a feasibility computation using the original HR proof, not a claim of a new resonance theorem.

To make Source345 uniform, fixed-degree filling must also be made uniform without taking a uniform g-injectivity radius. Its local path recipes can be taken in h; a g-unit-length piece has h-length <=1/u. The bounded prototype homotopies have g-length <=v times their h-length. Spokes can likewise be chosen in h and retimed using g-arclength. The source coloring argument then gives degree-dependent a_j,H_j uniform in g. At the bounded terminal level b_j, the cycles lie in the reference h-length sublevel b_j/u; filling there and comparing back gives a uniform bounded remainder. A detailed proof and the required constants will be added after completing the relevant primary comparison.

## Parameter-family warning and explicit route

Pointwise or even uniform fiberwise death does not imply total-space death. For a smooth scaling family g_t=f(t)^2 h_round on [-1,1], with f(+-1)=1, f(0)=b>1, monotone on each half, a high-degree loop class of round critical length c produces two parameter-end cycles. Their difference is global-null in [-1,1]xLambda. At a<c*b, the middle fiber may not carry the class, obstructing a filling between the ends. At a>c*b, the product cylinder fills. This can create bars of length (b-1)c in the parameter total space although each round fiber is perfect. The remaining work is an exact Mayer--Vietoris argument at open cuts, with degree, critical-value and constants-relative conventions explicit; no claim of geometric image counting is intended.

A compatible stronger route is to normalize the global mean-frequency scale across the parameter family. Any such route must prove a total-chain filling mechanism, not assume that fiberwise arbitrary fillings vary continuously. The relation between parameter homological degree and loop degree must be carried explicitly. This is an exploratory direction, not a frozen theorem or an assertion that a bridge is unpaid.

## Transition to the frozen candidate (recorded after proof drafting)

The paragraphs above retain their original prefreeze status and feasibility wording. After reading the additional NR section 8 and Shelukhin sections 3.1--3.2 comparisons, the candidate was frozen at 2026-10-24T12:05:20.406649+00:00. FROZEN.md is 3402 bytes, SHA256 0031fe7106971855b2c1b98e3e1bc40574ed249ad8b17e9ac028d1f30bfae1ce; its bytes have not changed. PROOF.md then developed the whole frozen scope.

The completed construction uses a good cover of order p+1 and the singular-chain Cech resolution. Below the lowest possible essential birth it kills absolute local maps; above the highest possible birth it kills local pair maps. A composite of p+1 zero maps on the relevant E1 diagonal kills the total map by its finite filtration. Tracking the transition interval gives beta_k <= k*(lambda_+-lambda_-)+(2p+3)D_0+lambda_++p*lambda_-+2R. No continuous choice of a fiber filling is used. The two-ended round scaling family supplies beta_(n+2m(n-1)) >= 2*pi*m*(b-1), and hence the same asymptotic coefficient. Nonhomothetic constant-frequency families are obtained by continuous frequency normalization of a conformal deformation with nonconstant scalar curvature.

After the freeze and first proof draft, a second, narrower construction-alias history scan used exactly the same pruning and found zero eligible matches. It did not read any original history body and does not establish clearance. Postfreeze rereads of source shortening lines 139--298, source ordinary lines 1--159, and HR section 5 lines 632--818 checked the already-read uniformity interfaces; their exact extents and timing are recorded. No new theorem hypothesis or conclusion was added to or removed from the frozen statement. The initial dimensionless resonance feasibility estimate above was superseded in the proof by a deliberately looser uniform length-error bound R_box, then divided by u*lambda_h.
