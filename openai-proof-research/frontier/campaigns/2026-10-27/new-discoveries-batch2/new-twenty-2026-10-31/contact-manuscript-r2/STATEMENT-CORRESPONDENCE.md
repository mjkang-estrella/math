# Source and formal correspondence

## 6. Formal statement and correspondence

For a reduced expression phi=q/p with p stable and q a unimodular multiple of its reflection, use the face |Z|=1, |W|<1. At a torus point (tau1,tau2) with q(tau1,tau2)=0, local contact K means the following exact quantifiers. First fix c>0, C>0 and rho0>0. There exists delta0>0 such that for every unit Z with 0<h=|Z-tau1|<delta0 and EVERY disk zero v of q(Z,v) with |v-tau2|<rho0, c h^K <= 1-|v|. Also, for EVERY 0<rho<=rho0 there exists delta>0 such that for every unit Z with 0<h<delta there EXISTS a disk zero v with |v-tau2|<rho and 1-|v|<=C h^K. The constants c,C,rho0 are fixed before both clauses; only the upper parameter interval may shrink with rho. In particular C cannot depend on rho, and an empty local zero set cannot supply the upper witness.

This compares the local zero-height infimum with h^K in arbitrarily small neighborhoods. Here (tau1,tau2)=(-1,1). Section 3.1 and Remark 3.2 of [2] retain the maximum branch convention in the ELA 2026 journal version: generic matched level curves yield the maximum of their vanishing orders. It is neither the minimum nor their sum.

The Lean namespace is ContactPilot. SourceContactLocal.lean defines HasLocalZeroSetContact with exactly the fixed c,C,rho0, all-root lower bound and every-rho upper witnesses of Section 1. ReducedCertificate f stores the numerator, nonzero denominator, common-divisor reduction, stability, representation of beta composed with f composed with betaInv, bidegree bounds, unit phase and reflection identity. NearestWDistance requires an attained w-reaching walk of length d and minimality among all such walks.

SourceConjectureLocal quantifies every n, simple graph G on Fin n, Boolean coloring isZ, root i, certificate cert for graphFunction G isZ i, and natural d,K. Its implication is

    NearestWDistance G isZ i d -> 0<K -> Even K ->
    HasLocalZeroSetContact (eval2 cert.numerator) (-1) 1 K -> K=2*d.

The operative endpoint is ContactPilot.refutationLocal : not ContactPilot.SourceConjectureLocal. It applies the universal hypothesis to the five-vertex certificate, d=1 and K=6, using nearest_w_one and bidisk_local_contact_six, and contradicts 6=2. The graph is connected, has both colors and a z root. No residual branch or certificate hypothesis remains.

Correspondence table (declaration - meaning):

    resolventMatrix, graphFunction - color-diagonal matrix, inverse entry
    beta, betaInv                - half-plane / disk coordinates
    ReducedCertificate, reflect  - reduced rational-inner representation
    HasLocalZeroSetContact       - local zero-height comparison, Section 1
    local_contact_unique         - uniqueness for arbitrary q and torus point
    NearestWDistance             - attained shortest root-to-w walk length
    SourceConjectureLocal        - universal nearest-w implication above
    refutationLocal             - negation of that implication

The branch chain QuadraticBranches -> ExactOrders -> SecondBranch -> BranchBounds -> HalfPlane constructs analytic roots and exact orders. GraphResolvent ties N/Q to the matrix. Coprimality and CayleyPolynomials through BidiskCertificate supply the reduced certificate. RootLocalization, CayleyLocalization and CircleChart give localization and coordinate transfer. LocalBidiskContact proves bidisk_local_contact_six, reusing only the valid lower estimate from HISTORICAL bidisk_contact_six in BidiskContact.lean. ContactUniqueness proves local_contact_unique; RefutationLocal proves bidisk_not_local_contact_two and refutationLocal. The new upper proof uses half_plane_contact_six_localized, not a coercion from the old predicate.

## 6.1. Existence, uniqueness and the source bridge

For arbitrary functions q, arbitrary torus points and natural orders, local_contact_unique proves uniqueness. Combine the lower bound of one order and the upper witness of the other inside min(rho1,rho2), with a common sufficiently small parameter interval. If K1<K2, then c1 h^K1<=C2 h^K2 is impossible as h tends to zero through positive circle displacements. circle_punctured_small supplies those displacements at every unit point; the parameter domain is not vacuous. Swapping the orders gives equality. This theorem does not assert existence of any contact germ.

The ordinary existence bridge uses the source's LOCAL infimum/maximum-branch convention. Isolate the finite local numerator-root cluster at tau2. Its branch heights have positive power comparisons. Their maximum exponent K_src gives a lower bound for every branch, after restricting h<1, and an upper bound on a branch attaining that maximum. This branch tends to tau2, so it enters every smaller neighborhood with the same comparison constant. Roots outside the cluster are excluded by first shrinking rho0 and then delta0. Thus whenever the source order is defined in this sense, it satisfies HasLocalZeroSetContact. Conversely its two clauses compare the local infimum with h^K, and uniqueness prevents a different exponent. Graphs without such a germ are outside this explicit hypothesis; no invented order is assigned.

This is an ordinary statement-correspondence argument, not a general Lean analytic-contact existence theorem. Reduced representations of the same rational function differ by scalar units; enlarged reflection bidegrees allow monomial local units at (-1,1). These changes cannot create another local exponent. The input Cayley map sends (infinity,0) to (-1,1) independently of the graph; it does not assert a singularity for every graph.

For the actual counterexample, the exhaustive analytic branches in Sections 4-5 independently establish existence and K_src=6. The source conjecture would give K_src=2 for this graph, a contradiction. More generally the source conjecture implies SourceConjectureLocal by the preceding ordinary existence bridge and uniqueness. Calling an arbitrary contact hypothesis a restriction would not by itself justify that implication.

HISTORICAL: HasZeroSetContact, HasHalfPlaneContact and ContactPilot.refutation (negating the old SourceConjecture) belong to the r5 chain. Review r2 failed general locality: one existential radius could let an upper witness come from a different boundary cluster, even allowing orders 2 and 6 at the same named point. The root ruling agreed and held acceptance. The five-vertex mathematics survived because its roots actually localize. The r6 repair fixes the lower neighborhood and requires an upper witness in every smaller neighborhood with the same C. Review r3 passed A, B and bounded C, with D qualified pending manuscript integration. Historical declarations remain in the packet for provenance; they are not the operative local definition or endpoint.

## 6.2. Diagnostic locality regression (ordinary, non-Lean)

Let p6=p_b and q6=q_b be the pair of Section 5, and use the reviewer's diagnostic

    p*(Z,W) = p6(Z,-W)(2+Z-W),
    q*(Z,W) = q6(Z,-W)(2ZW+W-Z).

The preserved exact regression verifies reduction and bidegree-(4,3) reflection. Stability follows from stability of p6 and |Z-W|<2 in the open bidisk. At Z=-1 the first numerator factor is -8i(W+1)^2, nonzero on the compact closed ball |W-1|<=1/2. Uniform continuity excludes that factor's zeros there for Z sufficiently near -1. Every local zero therefore comes from the linear factor, with unique root v(Z)=Z/(2Z+1). It tends to 1 and thus enters every positive neighborhood of 1.

For |Z|=1 and h=|Z+1|>0, |2Z+1|^2=1+2h^2, so

    1-|v(Z)| = 2h^2/[sqrt(1+2h^2)(sqrt(1+2h^2)+1)].

For h<1 this lies between h^2/3 and h^2, since the denominator is at least 2 and at most sqrt(3)(sqrt(3)+1)<6. The root lies in the disk for h>0. Take rho0=1/2, c=1/3 and C=1, and shrink delta0 for separation and h<1. The upper witness enters each rho in (0,rho0] after shrinking delta, preserving C=1. Hence the diagnostic has local order exactly 2. An alleged order-6 upper witness in the separation ball would force h^2/3<=C h^6 for arbitrarily small h, impossible. This also illustrates general uniqueness.

This diagnostic is an ordinary analytic argument with exact symbolic algebra, not a Lean theorem. No graph-resolvent realization of the product is asserted. The old predicate could borrow the remote order-6 cluster at -1 through a large radius; the repaired predicate cannot. See REGRESSION.md and the preserved r6 regression log for the full provenance.

## 7. Verification and trust limits

The repaired r6 source-only packet contains 33 Lean modules: 28 unchanged historical r5 modules and five additions, SourceContactLocal, ContactUniqueness, LocalBidiskContact, RefutationLocal and AuditR6. The delivered contact-source-only.zip is a byte-identical copy of contact-formal-r6/contact-r6-source.zip. Its SHA-256 is

    e92d6eceaf79972064c2f142a9cd1c4b3df45b520d1eed0445f288cddc1270d6

The pin is Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The portable r6 driver refuses existing local compiled objects or a pre-existing build directory, compiles serially with -j1 and -DwarningAsError=true, invokes leanchecker separately per module, and inventories declaration types and opaque-inclusive bodies as expression DAGs. It rejects unsafe/partial declarations and transitive axioms beyond propext, Classical.choice and Quot.sound.

Supplied r6 evidence, preserved under evidence/r6/fresh-extraction/replay-logs, reports 33 strict builds, 33 checker calls, 323 declarations and 17 failing negative controls. complete.json binds the 33 source hashes; negative-controls-reviewed.json records the actual failures, including old-to-local shortcuts, wrong local order and reversed local refutation. The AuditR6 declaration DAG and audit inventory record allowed-axiom checks for refutationLocal, local_contact_unique and bidisk_local_contact_six. These are supplied r6 replay records, not computations run by this manuscript lane.

Review r3 independently checked the 26-module endpoint closure, one endpoint checker and three axiom prints. It explicitly did not run a full packet replay or all negative controls. Root's decisive fresh replay remains PENDING and is not claimed here. This lane ran no Lean or lake. The r6 driver caps each call at two CPUs, CPU 120 s, wall 140 s, sampled private memory 6 GiB and MALLOC_ARENA_MAX=2; manuscript generation uses the same CPU/wall ceilings and sampled total process-group RSS. REPRODUCE.md points to the r6 driver. The full dossier binds paper, sources, reviews, source receipts and replay records with SHA-256 hashes; no compiled objects are packaged.

Kernel checking cannot establish prose-source fidelity, dependency-binary provenance without a dependency-source rebuild, or literature-search completeness. Cached package binaries remain trusted. The inventory and controls supplement checking and independent review. The ordinary proof above is readable without trusting a search script. No new novelty clearance or acceptance is claimed; root decides and credit remains zero.

