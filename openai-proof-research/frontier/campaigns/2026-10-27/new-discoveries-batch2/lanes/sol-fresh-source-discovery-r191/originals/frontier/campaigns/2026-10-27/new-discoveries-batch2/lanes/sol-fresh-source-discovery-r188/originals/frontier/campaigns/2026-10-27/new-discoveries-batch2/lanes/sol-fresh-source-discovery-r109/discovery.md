# r109 — full unbalanced-join question; UNRESOLVED, credit 0

Counts remain 8 additional / 38 total. No PROOF.md, Lean endpoint, manuscript, nomination or shared-file change. All helpers ran under the unchanged packet/helper_guard.py (AS/group RSS 512 MiB, CPU210, wall230, nominal40ms, BLAS1). The initial optional bs4 extraction failed because bs4 is absent; its script and error are preserved, and the replacement uses only the standard library. No caps were raised.

## Early all-date screen and selection

The ancestor/batch AGENTS, ledger, NEXT, prior-campaign-context, pinned upstream and catalogue were consulted. Two streaming passes examined 125986 and 125988 artifacts, respectively; no read errors. File selection includes all dates, every SUMMARY/discovery/FINDINGS/PROOF/review/ledger filename, SCREENED-OUT*.md, openproblem files, tools/scripts/agent paths, and complete copied review text trees. Each file is hashed incrementally, never concatenated into an aggregate source buffer. Literal arXiv-ID regex assertions execute before scanning. The second pass preceded sustained investment in the join problem. New concurrent files account for inventory-size changes. These are bounded local snapshots, not semantic registry clearance.

Three primary-source families were screened using actual current arXiv bodies and submission histories:

1. Tokmachev, 2607.08869v1 (9 July2026), introduction equations(4),(5): all-dimensional interior/boundary mean distance comparison, and planar boundary mean distance >perimeter/6. EXCLUDE, already screened in r69/r95 and publicly resolved/refuted. The actual r95 report explicitly excludes the latter, not merely a related Gaussian question. Shen2608.06470v3 was fetched and its proof body read: Section5 Theorem5.17 and the half-boundary/Gini/median-of-three argument, plus the dimension-lifting discussion. Cached extraction labels differ from r95's older paragraph numbering; no theorem-number identity is assumed. No audit of Tokmachev's ancillary multivariate projection lemma is nominated.
2. Fryš–Kotrbatý, 2609.08612v2 (17 September2026), Conjectures1.2/1.3: all n,p and all multiindices of the higher-order Godbersen inequality. EXCLUDE public proof. Fryš–Kotrbatý–Mouamine–Wang2610.06806v2 (12 October2026), Theorem1.5, Proposition3.1 and its actual proof settle the inequality; the face-lattice reduction treats equality. In Proposition3.1 equations(17),(18), the shear Phi and the product projection formula convert the target to a mixed volume in (p+1)n dimensions; replacing the diagonal by K^(p+1) gives exactly the desired multinomial constant. This is a full public body, not an abstract. Conjectures1.8/7.7 consequently are routine nonnegative mixed-volume expansions and are excluded too.
3. Mielke-Sulz2609.13517v1, main result: Petty for all bodies of revolution. EXCLUDE public proof (and the full Petty family is already in the pinned OpenAI catalogue, family088). Actual source sections3–4 reduce to T(b_g)/T(b_0) >= [I(b_g)/I(b_0)]^(n−1), use determinant factorization and Hölder, and handle profile measures for nonsmooth equality. Neither the restricted nor general Petty claim is fresh credit.

The distinct remaining statement in source2 is selected below. The broad Godbersen hit in r103 explicitly describes an unselected search lead, not an attempted join proof. Expanded join screening also catches copied SCREENED-OUT-R71; the actual hit is Rédei's finite abelian factorization theorem, unrelated to this geometry. r69/r95 hits are the distance exclusions above. Tree-path hits and an author bibliography do not supply actual matching proofs. No exact earlier local attempt at Conjecture1.11 was identified in the frozen selected corpus. This is a local duplicate-screen conclusion only.

## Exact selected full source statement

Fryš–Kotrbatý2609.08612v2, Conjecture1.11. For every integer n>=2, p>=1, full-dimensional compact convex K in R^n and t in[0,1], there exists x in K such that

    |conv(-t Delta_p(K-x), (1-t)(K-x)^p)| / |K|^p
      <= |conv(-t Delta_p S, (1-t) S^p)| / |S|^p,

where S is a centered n-simplex, Delta_p y=(y,...,y), powers are Cartesian products, and volume is np-dimensional. Translation x may depend on K,p,t. There is no symmetry, smoothness or fixed-centroid restriction. The source asserts an inequality here, not an additional equality classification. The two endpoints are included but are not the substantive target. We do not replace this statement by mixed-volume inequalities, Conjecture9.3's different join, or one fixed p/n/t.

Source Lemmas8.1/8.2 give the entire simplex comparator:

    C(n,p,t)=(1-t)^[n(p-1)] max_{0<=j<=n} binom(n,j)t^j(1-t)^(n-j).

For 0<t<1 a maximizing j is floor((n+1)t), with tied adjacent values at integer thresholds. This follows also from the ratio of consecutive binomial terms. Classical predecessor Artstein-Avidan–Einhorn–Florentin–Ostrover1408.2135v1, Conjecture1.2 and Lemma2.1, supplies precisely the p1 conjecture/comparator. Its Section4 treats the plane. We read the actual classical body, including Theorem1.5 and its proof mechanism; its universal any-origin estimate is weaker than the centered-simplex comparison. The source's higher-order Lemma8.1 is a simplex identity, not a general-body identity.

## Sustained full-scope routes

A. Sharp public mixed volumes do not close the hull bound. Write Q=conv(A,B), A=-t Delta_p(K-x), B=(1-t)(K-x)^p. Since 0 belongs to A and B, Q is contained in A+B. Mixed volumes of this sum do not depend on x. Public higher-order Godbersen and multilinearity bound its normalized volume by

    M(n,p,t)=sum_{j=0}^n binom(np,j)binom(n,j)t^j(1-t)^(np-j).

At t=1/2, Vandermonde gives M=2^(-np)binom((p+1)n,n), whereas C=2^(-np)binom(n,floor(n/2)). Thus the loss is binom((p+1)n,n)/binom(n,floor(n/2)), strictly above1 for every n>=2,p>=1. All mixed-volume coefficients are already sharp for a simplex; merely strengthening those coefficients cannot repair this hull-to-sum step. Optimizing x after this step cannot change the bound, because every coefficient is translation invariant. This does not prove that no more refined use of mixed volumes can work.

B. The source's all-origin hull inequality (Theorem1.9) gives |Q|/|K|^p <=(1-t)^[n(p-1)]. At t1/2 its loss relative to C is 2^n/binom(n,floor(n/2))>1, independent of p, and remains unbounded as n grows. Equality is attained for a simplex at a vertex. Picking an arbitrary x, or applying this inequality at a minimizer without a new estimate that uses minimizing geometry, therefore leaves a genuine uniform gap. Source Proposition8.3 proves join=>mixed volumes; reversing it from the new public mixed-volume theorem is invalid.

C. Fibre reduction and its obstruction. The determinant-one shear

    F(y1,...,yp)=(y1-yp,...,y[p-1]-yp,yp)

has fibres in the product body K^p equal to

    C_w=K intersect (K-w1) intersect ... intersect(K-w[p-1]).

For w!=0, direct convex-combination elimination gives the exact Q fibre as the union, over 0<r<=1, of

    r(1-t) C_{w/[r(1-t)]} + (1-r)(-tK).

For a translated K use that translated K consistently in both places. This is a set identity, not a volume upper bound. For a simplex all nonempty C_w are translated homothetic copies with the explicit affine scale rho(w); source Lemma8.1 integrates those fibres to its exact comparator. For a general K that property fails. Already K=[-1,1]^2 and p2, w=(q,0), 0<q<2, give C_w=[-1,1-q]x[-1,1], with side lengths2-q and2. There is no scalar homothety of the square producing this rectangle. Fubini still gives integral |C_w| dw=|K|^p, but supplies no common control of the unions after adding -(1-r)tK. This failure persists over the whole interval q in(0,2), beyond the four check values. It is NOT a source counterexample: the square has other favourable geometry and is allowed a choice of x.

We also considered choosing x by minimizing the continuous normalized hull-volume functional on compact K. A minimizer exists, but existence alone yields no estimate of the minimum. A proposed differential/support-balance argument would have to control the moving hull's mixed facets and then prove a sharp global volume comparison; no such argument was established. We do not assume centroid optimality, differentiability at tied facets, or simultaneous optimal translation for all p/t.

## Exact validation and strongest objection

run.sh invokes the unchanged guard and check.py. The checker uses rational arithmetic only. It independently enumerates supporting facets and pyramid determinants for64 centered-simplex p1 hulls (n2..5; t numerator/7 and numerator/11). None are threshold nonsimplicial cases. It checks120 Vandermonde/loss identities (n2..16,p1..8), and four square-fibre obstructions. Guard PASS; these checks validate formulas/route failures, not the source conjecture. No general convex-body search or all-translation certificate is claimed.

Strongest objection: a proof must deliver a suitable translation for every K,p,t; all completed estimates above discard exactly that geometric information. The p1 statement already contains the full generalized Fáry–Rédei problem. The public Godbersen proof has the opposite known implication and cannot be promoted to a join proof. A refutation must certify some full-dimensional K,n,p,t for which EVERY x in K exceeds C, rather than exhibit a bad centroid or vertex.

Precise remaining gap: a uniform upper bound min_{x in K}|Q_{p,t,K-x}| <= C(n,p,t)|K|^p, or an all-x strict lower certificate for a concrete K. Neither is provided. This is UNRESOLVED, not substantive PASS. All ancillary reductions remain uncredited.

## Prior-art/access chronology

HTTP receipts include exact acquisition UTC, URLs, response headers, byte lengths and SHA256. Current arXiv bodies are lawful new primary evidence, not a current registry inventory or priority claim. Latest abstract histories were checked; primary HTML version identifiers were read. The source2 conjecture (September) predates its mixed-volume successor (October); this establishes public-proof exclusion for mixed volumes, not proof of the distinct join conjecture. No new registry call was made. r106's two HEAD403 at20:10:44–45 and r105 recursive Omega403 remain controlling; no recorded reset information was located in those lane JSON/Markdown reports. Last supplied Omega73a5033dd654a16a14fcd1b13277f1a03d81d82619 at19:55:36 and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a are historical pointers. The18:13 complete path baseline, dated bounded chains and unresolved300 cap do not establish semantic/current absence. Live freshness remains HOLD. Search results are only leads until the actual named bodies are read; no absence-of-search-result clearance or absolute novelty claim is made.
