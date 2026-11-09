# MathDB 370092 — Fok primary-body and complete adaptation review

Review date: 2026-11-06 UTC. Recommendation: **EXCLUDE, credit 0**, because an authenticated 2014 source constructs the relevant irreducible Quaternionic representation, and the complete bridge below gives the candidate by specialization and elementary consequences. This is a demonstrated source-adaptation exclusion, not an inference from a familiar group name, proof shortness, or an abstract. Root alone adjudicates; accepted false; supplied campaign count 52/60 unchanged.

## Separate gates

| Gate | Verdict | Meaning |
|---|---|---|
| Independent ordinary mathematics | PASS preserved | Frozen r1 independent certificate reconciled; exact right-subspace endpoint remains valid |
| Literal statement / final EJLA | PASS preserved | Broad finite quaternionically irreducible alternative, final January 2026 p.18 Conjecture 1; no reflection-only solution claimed |
| Current correction investigation | BOUNDED PASS inherited | Completed r2 investigation; not repeated; no worldwide absence claim |
| Fok public body access | PASS | One public unauthenticated Adelaide file GET, HTTP 200 PDF |
| Fok identity / chronology | PASS | Actual published title/author/journal/date in PDF, not search metadata alone |
| Real-group convention / Quaternionic semantics | PASS | Example expressly uses trivial involution; Definition 2.20 matches commuting right-H structure |
| Exact representation matching | PASS | Actual complex eigenspaces and commuting J below, plus Proposition 2.24 uniqueness |
| Complete subsumption bridge | COMPLETE; novelty qualification FAIL | Old explicit construction yields actual finite unitary matrix group, repeated Q8 restriction, infinite right graph lines, and maximality among all containing subgroups |
| Qualified novelty / substantive campaign significance | FAIL for credit | Complete source adaptation is excluded by the task standard, even though the broad published conjecture is false |
| Pi recommendation | DO NOT DISPATCH / DO NOT EXECUTE | No dormant implementation plan: exclusion, not unresolved formal feasibility |

No Lean, axiom audit, replay, paper or acceptance claim is made. This review establishes no earlier verbatim published refutation of the 2025/2026 conjecture; the exclusion rests on the earlier construction and complete adaptation.

## Authenticated primary body and chronology

Chi-Kwong Fok, *The Real K-Theory of Compact Lie Groups*, SIGMA 10 (2014), 022, 26 pages, DOI 10.3842/SIGMA.2014.022. The article itself, printed p.1 (extracted lines 25–34), states received August 22, 2013, final form March 6, 2014, published online March 11, 2014. The institutional cover identifies this as the published version, retains the same DOI, and gives handle 2440/111698 and a cover date April 26, 2018. That cover date and HTTP last-modified in 2024 are not the article publication date. The body itself therefore authenticates a predecessor long before the September 2, 2025 target preprint and January 2026 final EJLA article.

The exact public institutional file was the already identified, previously unattempted lead:
https://digital.library.adelaide.edu.au/server/api/core/bitstreams/54262227-be1e-445a-9951-0495c404beda/content

One ordinary GET at 2026-11-06T09:11:00.154350+00:00 returned 200, application/pdf, 512290 bytes, SHA256 **6803da2ebfb938326734f6d389ac02aa09015b644fa5d4db6f24a461f18d0f03**. Saved as fok-adelaide.pdf; full response headers/status/hash in http-receipts.jsonl. The /api/ path was used only for this explicitly authorized public byte-file download, never an API query. Response cookie/token headers were passively recorded; no cookie jar, authentication, token reuse, POST, form, challenge, browser or access-control workaround was used.

Actual read: layout-extracted lines 1–620 of 1871, including cover/title/date, Section 2 scope, full Section 2.2 (printed pp.4–8), Definition 2.20, Proposition 2.22, Corollary 2.23, Proposition 2.24 and Example 2.25 through its ending. K-theory text outside this read range is not claimed reviewed. Section 2 permits arbitrary compact Lie groups; finite Q8×C3 is explicitly used, so the connected/simply-connected hypotheses of the main K-theory theorem are not imported into the representation classification. No mathematical reliance on that main theorem is needed.

Definition 2.9 defines a group involution and its compatibility with anti-linear structure. Definition 2.20 instead requires an anti-linear operator J with square −1; irreducibility is categorical, with morphisms respecting both G and J. Proposition 2.22 lists the paired complex-type construction; Corollary 2.23 relates its representation groups; Proposition 2.24 states uniqueness of compatible Quaternionic structure on a given complex representation and gives its doubling-isomorphism proof. Proposition 2.22's printed proof is only a reference to the preceding argument; Proposition 2.16 similarly refers to a standard proof. No unprinted full proof is claimed read. The specialized irreducibility argument below avoids depending on an unread external proof.

Example 2.25 expressly specifies **trivial group involution**. It identifies the faithful complex 2-dimensional Q8 representation rho_Q and the two nonreal C3 characters rho_zeta, rho_zeta². Its RH(G,C) list includes the paired complex representation
(rho_Q tensor rho_zeta) direct-sum (rho_Q tensor rho_zeta²)
with the compatible Quaternionic structure from Proposition 2.22. Thus its complex dimension is 4 and right-H dimension 2. This is not the different RH(G,R) item rho_Q tensor 1, which has right-H dimension 1. Nor does “quaternionic type” of a complex irreducible (Definition 2.19) mean the same thing as a Quaternionic irreducible object (Definition 2.20). The paired item is exactly the relevant one.

## Complete bridge to the actual matrices and exact endpoint

All deductions in this section are hand arguments, with no enumeration, solver or CAS.

**1. Right-H semantics.** Regard S=H as a right complex space using C=R+Ri. It has complex dimension 2. Left multiplication by q in Q8 gives its faithful complex representation rho_Q. Right multiplication J_S(x)=xj is complex anti-linear, squares to −1 and commutes with every left q. On V=H², let J(x,y)=(xj,yj). Under trivial group involution, a complex subspace is a right-H subspace precisely when it is also stable under J: C and j generate H. Likewise a complex-linear intertwiner commuting with J is right-H-linear. Thus the source's irreducible Quaternionic category matches the actual right-module category in this case. For a nontrivial group involution this argument would not apply; Example 2.25 has explicitly ruled that obstruction out.

**2. Actual representation and source equivalence.** Put c=−1/2, s=sqrt(3)/2, zeta=c+is. Let D(q)=diag(q,q), R=((c,−s),(s,c)). All act right-H-linearly; R has real entries and commutes with D(q) and J. On the underlying right complex vector space define
E_plus={(x,−xi):x in H}, E_minus={(x,xi):x in H}.
They intersect only at zero, have complex dimension 2 each, and sum to V. Left Q8 acts on each by x↦qx, while R acts by right scalar zeta on E_plus and by zeta² on E_minus. Indeed R(x,−xi)=(x zeta,−x zeta i), and the conjugate formula holds for E_minus. Consequently the underlying complex representation is exactly the paired item displayed in Fok Example 2.25, not merely one with a similar name or order.

J maps E_plus onto E_minus: J(x,−xi)=(xj,−xij)=(xj,(xj)i), using ji=−ij. It maps E_minus back and J²=−1. This gives an explicit compatible Quaternionic structure on the actual matrices. Fok Proposition 2.24 then identifies this representation with the Example's compatible structure up to a complex G-isomorphism commuting with J, hence a right-H-linear isomorphism by step 1. This uses the exact uniqueness statement on the matching complex representation, not a bare character comparison. A relabelling of the generator of C3 exchanges the two summands and changes nothing.

For completeness the specialized categorical irreducibility can also be checked directly. Left i on S has two complex eigenspaces, interchanged by left j, so S is complex irreducible. E_plus and E_minus are thus irreducible and nonisomorphic as complex G-modules, since R has different eigenvalues on them. Any complex G-invariant subspace splits into its intersections with these eigenspaces (the two spectral projections are polynomials in R), and each intersection is zero or the whole irreducible summand. J swaps the summands, so a J-stable such subspace is zero or V. Hence there is no nonzero proper invariant right-H subspace. This validates precisely the source construction's irreducibility in the required category.

**3. Faithfulness, finiteness and unitarity in the actual group.** Let
G_mat={D(q)R^a:q in Q8, a=0,1,2}, H0={D(q):q in Q8}.
Real entries ensure commutation. The identities c²+s²=1, c²−s²=c and 2cs=−s give R²=((c,s),(−s,c)) and R³=I. Both nontrivial powers have nonzero off-diagonal entries. Thus (q,a)↦D(q)R^a is a group homomorphism Q8×C3 into actual matrices, is injective (unequal exponents would make a nontrivial power of R diagonal), and its image is a subgroup. Hence |G_mat|=24, |H0|=8, H0 normal, quotient C3. Since |q|=1 and R is real orthogonal, every displayed matrix is quaternionically unitary. This supplies the actual faithful finite irreducible overgroup, not a formal direct-product proxy.

**4. Repeated restriction and real intertwiners.** Restricting the right-H representation to H0 gives S direct-sum S, on the two coordinate lines. A right-H-linear endomorphism of S has the form x↦a x with a=f(1). Commuting with left i and j forces a to commute with both, hence a is real. Therefore End_H0(S)=R, and the coordinate swap identifies the two equivalent copies. The restriction of the source's paired complex item is rho_Q direct-sum rho_Q, with precisely the right-H S direct-sum S structure just exhibited. No confusion between complex irreducibility and quaternionic irreducibility is involved.

**5. Actual infinite right subspaces.** The graphs of these real scalar intertwiners are L_t=(1,t)H, t in R, along with the vertical line L_infinity=(0,1)H. Each is a nonzero proper actual right subspace invariant under H0, since D(q)(1,t)=(1,t)q. Distinct parameters give distinct subspaces: equality forces (1,t)=(1,u)a, whence a=1 and t=u. Thus even n↦L_n gives an injection from N into the invariant lines; these are not merely infinitely many chosen generators of one line.

This is also the complete list. Any nonvertical line normalizes (x,y) on the right to (1,yx^−1). Invariance under D(i),D(j) forces its parameter to commute with i and j, whose common centralizer in H is R. Every nonzero proper right subspace of H² is a line: a normalized vector (1,t) and any vector outside its span eliminate to a nonzero vertical vector, then give both coordinate basis vectors. The vertical case is immediate by swapping coordinates. Thus this covers all potential invariant right subspaces.

As an additional direct check of step 2, R moves the vertical line; preserving L_t would require s+ct=t(c−st), so s(1+t²)=0, impossible over R. No division by c−st is used. G_mat is therefore irreducible in the literal required sense by either argument.

**6. ALL intermediate subgroups and maximal reducibility.** For any subgroup K with H0≤K≤G_mat, finite index multiplication gives 3=[G_mat:K][K:H0]. Primality implies K=H0 or K=G_mat. Equivalently an element outside H0 supplies R or R² after multiplying by D(q)^−1; either generates C3. No assumption that K is normal or belongs to an enumerated list occurs. H0 is reducible (it preserves the horizontal line); G_mat is irreducible. Therefore H0 is maximal among ALL reducible subgroups of G_mat, while fixing infinitely many right lines.

**7. Credit implication.** The representation in step 2 is already explicitly listed in the 2014 body for this exact finite group with this exact involution. Steps 3–6 supply the full faithful unitary realization, repeated restriction, graph family and prime-index argument required by the target. These are direct consequences of that construction and elementary group/module facts. Accordingly the complete existing-construction/source-adaptation exclusion applies. The article need not have named a conjecture published eleven years later. We do not claim Fok stated maximal reducibility or the later refutation verbatim. The basis for exclusion is the demonstrated complete bridge, not a conjectural missing bridge or the ease of the arithmetic.

## Inherited evidence, limits and integrity

Read and reconciled completed r2 REVIEW.md, review.json, search-log.json, source-read-inventory.json, all http-receipts.jsonl and root parent integration-r2. Also read the named completed r1 independent REVIEW and r326 ORDINARY-370092. Their math and literal/final EJLA PASS survive. Older HOLDs about this precise Fok example are now resolved by primary-body access and the bridge. Earlier broad historical wording in r326/r1 is superseded by the narrower completed r2 coverage and this result. No other mathematical target was reopened; integrity hashes alone do not imply mathematical review of all frozen files.

Search budget: **0 new managed search batches, 1 new normal public GET**, no HEADs, retries or additional leads. No EMIS 406, MIT 403, Nebe TLS or failed journal route was revisited. No global priority claim is inferred from r2 search nonhits. Generic Clifford-literature coverage is not a blocking residual, and no open-ended chase was attempted.

Frozen-inputs: **139/139 matched before mathematical reads** in frozen-before.json; frozen-after.json records the final recheck. No previous source/review/proof bytes were edited. Protected active expanded-corpus-r327 and all crown-vnumber paths were excluded from any read/hash/glob/poll. Only the named frozen allowlist and assigned lane were accessed. All output writes are in this lane. No children/delegation, Lean, mathematical search/enumeration, solver, CAS, git, shared/author/dependency write, paper, publication, contact, upload or account action occurred.

Resources: exact first command ran bootstrap with its own pre-read affinity/CPU/AS caps and preserved bootstrap-receipt.json. All later local Python commands used -I -B, selected at most the first two allowed CPUs, set CPU≤120 seconds and address space≤6 GiB before substantive work, with external timeout≤140 seconds. pdftotext inherited caps, had a 25-second timeout and was synchronously reaped. resource-jobs.jsonl gives measured self CPU/high-water RSS and child usage for helper jobs; bootstrap has its own receipt. Initial bounded inspection/helper-writing/artifact-writing jobs have command completion/wall evidence and configured caps, but some lack persisted per-job RSS measurements. No group/cgroup/managed-service telemetry or aggregate peak is claimed. No managed search service was used. All launched jobs finished and were reaped; no background work remains. Resource exceptions/telemetry limits are stated in RESOURCE-EXCEPTIONS.md.

Artifacts: REVIEW.md and ID-keyed review.json are the decision packet; source-read-inventory.json and search-log.json define coverage; http-receipts.jsonl preserves exact response details; source PDF/text retain the authenticated evidence; frozen-before/after preserve integrity; resource-jobs.jsonl and bootstrap receipt document measured resources. MANIFEST.sha256 covers lane files other than itself. Root alone may integrate/adjudicate; no execution plan is supplied for this excluded candidate.
