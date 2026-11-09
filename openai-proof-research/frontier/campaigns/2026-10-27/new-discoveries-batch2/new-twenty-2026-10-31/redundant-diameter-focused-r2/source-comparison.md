# MathDB 362436 — focused qualification continuation

2026-11-01. Recommendation: **HOLD on a newly identified, concrete unread product-family comparator.** No novelty PASS, routine-result exclusion, root acceptance, or accepted credit is claimed. Ordinary fidelity and mathematics retain the independent r1 PASS. Significance remains substantively eligible conditional on novelty. The conditional gate for sustained Lean work is **not met**; no new Lean compilation or endpoint is represented here.

## Bibliography: dispose of the unsupported 2017 claim boundedly

The exact raw row has `first_stated_year: null`, `documented_by_year: 2017`, and explicitly associates its alleged second occurrence with arXiv:1709.03974. The cached actual paper is Cain–Malheiro, *Combinatorics of cyclic shifts in plactic, hypoplactic, sylvester, Baxter, and related monoids*, v1, 12 September 2017. Its graphs describe cyclic shifts of monoid elements and its diameter bounds concern rank and evaluation classes. That is not the distance-redundancy conjecture. Thus the **specific asserted bibliographic binding is erroneous**. It provides neither an earlier graph occurrence nor an unresolved obligation to locate an unspecified 2017 paper indefinitely.

Steane 2403.16197v1 Section 2 explicitly says that “surrounds” is introduced there and in reference [10]. Reference [10] is *Threat, support and dead edges in the Shannon game*, arXiv:1210.7985v1 (30 October 2012). The r1 cached primary body defines the open-to-closed surrounding relation before Theorem 7; Theorems 7 and 14 concern threats/support and dead edges in the Shannon game. Rerouting a winning colored path does not preserve all shortest distances after arbitrary vertex deletion. It is not a prior statement of the logarithmic diameter conjecture. The 2024 paper's introduction describes applying the Shannon-game idea to distance and isometric operations. Its bibliography contains no identified 2017 predecessor for this conjecture.

A new bounded OpenAlex query `Steane graphs 2017` was noisy (quantum-code results); no specific real 2017 predecessor was recovered. This is weak negative evidence, not proof that no publication exists. **Recommendation: treat the raw row's 2017 attribution as bad metadata; use the verified March 2024 statement chronology, without asserting first-in-world priority.** The missing unidentified 2017 paper is no longer itself a reason to hold the candidate. No database edit was made.

The inherited live arXiv abstract at 15:32 UTC lists v1 only and no journal reference. Inherited Crossref/OpenAlex lookups did not identify a Steane journal version. No journal version is invented, and no worldwide absence is claimed. An unspecified hypothetical journal is not promoted to a concrete unread body.

## Actual new primary comparisons

Saved PDF bodies, extracted text, exact URLs/UTC/status/bytes/SHA256 are in this lane. Successful downloads were public HTTP, without accounts, tabs or contacts. These are primary-body comparisons, not abstract clearance.

### Hu–Xu: the diameter ingredient really is prior

Fu-Tao Hu and Jun-Ming Xu, *On the diameter of the Kronecker product graph*, arXiv:1204.4014v1, 18 April 2012; metadata also identifies DOI 10.12785/msl/020206. Read definitions, Lemmas 2.4–2.5, Theorem 3.2 and complete proof, Theorem 3.3, and Theorem 3.6 and its proof. The graphs allow loops, but the applicable factors here are loopless.

Their exponent gamma(H) is the least threshold such that every ordered pair has a walk of every length at least gamma(H); infinity if no threshold exists. Theorem 3.2 assumes both factors connected with diameter at least one, with the first containing an odd cycle. Part (1) gives the projection lower bound. Part (4) gives an upper bound by max{gamma(G1)+1,diam(G2)}, with equality when G2 is bipartite (the symmetric other bound is included in its statement).

Apply **G1=K4, G2=C12**. K4 is connected, has triangles, diameter 1 and gamma=2: a two-step walk uses a third label, a three-step closed walk uses a triangle, and all larger lengths follow by two-step excursions (and prescribed endpoints are handled the same way). Gamma is not 1 because loops are absent. C12 is connected bipartite, diameter 6 and gamma=infinity. Therefore Theorem 3.2(4) yields **diam(K4 tensor C12)=max{3,6}=6**. This is a genuine exact prior diameter theorem, including connectedness through Lemma 2.4. It makes the candidate's diameter ingredient a standard instance; it is not a prior full refutation by itself.

Theorem 3.6 gives a similar formula for complete t-partite H, t>=3. Its short proof says d(H)>=2, which needs care if singleton parts are allowed (K4 has diameter 1). We avoid that wording issue entirely by the explicit Theorem 3.2 application above. This does not undermine the relevant bound or justify silently strengthening the printed proof.

No result in these inspected passages asserts all surviving-pair distances after a vertex deletion, no-surrounding, or a counterexample to Steane's 2024 conjecture. Ordinary connectivity is weaker than distance preservation. We do not claim all cited connectivity literature was read.

### Mondal–Atik: the exact distance table is also prior

Priti Prasanna Mondal and Fouzul Atik, *On the distance spectrum of the Kronecker product of distance regular graphs*, arXiv:2411.19784v1, 29 November 2024. Read graph conventions, Lemma 1.3, Theorem 1.2, and **Theorem 4.1 with its complete proof**, pp.12–14; inspected the concluding remarks and bibliography for its dependency. Theorem 1.2 cites Hu–Xu. Its printed small-diameter threshold branches overlap at gamma=2; our comparison uses d=6 and the original Hu–Xu proof instead.

Theorem 4.1's proof writes D(K_n tensor C_(2m)) as a block matrix indexed by the complete-graph label. Diagonal blocks are **2A+D**, off-diagonal blocks **2I+D**, with A,D the cycle adjacency and distance matrices. With n=4,m=6 this is exactly the candidate's full distance function: equal labels and adjacent layers have distance 3; equal layers and different labels have distance 2; otherwise nonzero distances are cycle distances. The source then diagonalizes this block matrix to derive the spectrum. We rely on the displayed matrix for comparison, not its spectral calculation as a proof of redundancy.

Crucially, the matrix is for the intact product graph. Removing one vertex produces a graph which is not itself K_n tensor C_(2m); one cannot apply the formula again to obtain its induced-deletion distance matrix. The paper's inspected proof and concluding discussion do not assert the deletion invariance or no-surrounding hypothesis. Thus it supplies a second substantial existing ingredient and an especially close prior construction, but no verified full-scope bridge yet.

### Lakshmi: mixed-factor product, different invariant

R. Lakshmi, *Optimal orientation of the tensor product of a small diameter graph and a complete graph*, Australasian Journal of Combinatorics 50 (2011), 165–169. Read the entire five-page primary body. Theorem 2.1 assumes diam(G) in {2,3} and a Z2_n-family containing chi'(G) sets. It establishes an orientation attaining the undirected diameter. C12 has diameter 6, and the candidate uses n=4; the sufficient families and corollaries are not the candidate's hypotheses. “Strong orientation” means directed reachability, not Steane's all-redundant graph. The proof never deletes arbitrary vertices or proves source surrounding conditions. The cited 2009 Ars Combinatoria article on optimal orientations of tensor products and circulants is not read here; no fault-distance result is inferred from that title.

## Test the possible whole-result bridge explicitly

For simple A tensor K_q, common neighborhoods factor as sets:

N((x,a)) intersect N((y,b)) = (N_A(x) intersect N_A(y)) times (N_Kq(a) intersect N_Kq(b)).

The second cardinal is q-1 for a=b and q-2 for a!=b. Hence for q>=4 no common-neighbor count can be one. Combined with Steane Lemma 4.1 this proves all vertices redundant, without assuming A strong. This is an explicit elementary mixed-factor derivation, independently checked here; it is **not** represented as a located prior printed mixed-factor theorem. It also covers coincident first coordinates, where the first factor's count is its degree.

The other source hypotheses still require verification: for regular C12 tensor K4, source Lemma 2.1(iv) reduces surrounding to twins, but the absence of weak AND strong twins must still be established. Neighborhood separation for C12 and unequal complete labels supplies that verification, as in the ordinary proof. Hu–Xu supplies the final diameter ingredient. These observations sharpen the routine-adaptation question considerably. **They do not establish historical full-scope subsumption solely because all steps are elementary.** No inspected prior body states that all these ingredients coexist as a bound violation or provides a product theorem encompassing both redundancy and no-surrounding. Conversely, we make no positive non-routine certification. Root must adjudicate substantive qualification after the remaining concrete comparator is resolved.

Inherited comparisons remain valid for their actual hypotheses: Steane 5.1(ii) requires two strong factors (C12 fails); Steane 2.6 requires both factors have no surrounded vertices (K4 fails). Cooper–Tauscheck 2025 Proposition 5(2) requires two distance-critical factors (K4 fails). Not-all-critical is not all-redundant. The new diameter comparison does not repair those hypothesis failures.

## Newly identified unread material body: the conditional gate stays closed

**Pranava K. Jha, *A family of efficient six-regular circulants representable as a Kronecker product*, Discrete Applied Mathematics 203, 72–84, DOI 10.1016/j.dam.2015.09.007.** OpenAlex identifies an online date in 2015; no independently verified issue-date chronology is asserted. It predates this investigation either way. Its full text is material to check because it explicitly concerns six-regular Kronecker-product networks and their efficiency/distance structure, close to the candidate's degree-six cycle-product construction. We have not established that its family includes C12 tensor K4, nor that it proves redundancy. Those are the exact missing comparisons, not conclusions drawn from metadata.

The indexed publisher PDF URL returned **HTTP403** at 15:43:48 UTC; the full denial body and receipt are preserved as `circulants.body` and `circulants.receipt.json`. It is not a PDF or theorem evidence. No retry, alternate publisher challenge route, account action or bypass was attempted. The exact-title OpenAlex result has a single publisher location and `any_repository_has_fulltext: false`. This is not proof that no lawful author copy exists; no distinct publicly identified body route was found in the bounded check. No credentials were requested or used.

**Obligation:** obtain an independently lawful primary body, identify its exact product factors/parameter ranges, distance/routing/failure statements, and compare them with every-surviving-pair deletion preservation and open-to-closed no-surrounding. If its theorem plus explicit ordinary bridges already yields the full bound refutation, exclude with zero credit and stop formal investment. If its family/invariants are inapplicable, record the exact reason and revisit bounded qualification. An abstract or title cannot discharge this obligation. This is a concrete finite next step, not an endless search for an unidentified predecessor.

## Live registries and access bounds

Fresh `/commits/HEAD` at 15:44:59 UTC: OpenAI/math remains 4eaee87548250b2682affda7d05d947c05554bae. Omega is now a5ff0772b0ceeb6c8e05456bbc057fec5489e1fc. The fresh root gives D5 dc94715eb7700d822e91cbf264fd1efbbe36906e and unchanged Problems 0b45ced5e033ab15556c8f7a9177458bc5ad1de6. A fresh untruncated recursive D5 listing was compared with the complete r1 cached listing; `registry-delta.json` records every change. Changed blobs concern Robin crossing prices, fermionic quantum constructions, an interval measure representative, and a Weil/Mertens bound. No changed graph-target path was found. This is scoped path/blob evidence only; it is not repository-wide body clearance. The r1 actual RedundantLeafMatching body comparison is retained as an inherited independent review, not a new proof audit by this worker.

General web/connector 401 routes, stopped Crossref 429 route, inherited MathDB/Palomar403 routes were not retried. OpenAlex queries in this lane are metadata leads, not primary evidence of a theorem's scope. The source and comparator body hashes, access results, and chronology are all bounded to saved receipts. Protected/accepted families remain excluded. No shared ledgers changed.
