# Independent preliminary review of frozen Kazemi hypercube candidate

Recommendation to root: **EXCLUDE as a routine source bridge under the strict campaign standard**, with a complete ordinary mathematical proof surviving this review. This is an eligibility judgment, not evidence of an earlier published proof. The weighted-capacity inequality is not explicitly stated in the inspected sources. Its derivation and use are given below so that root can adjudicate the judgment independently. No acceptance, formal verification, worldwide novelty clearance, or count change is asserted.

## Scope and custody

I worked solo and wrote only in this review directory. `prepare.py` verifies all 34 absolute source paths against `root-r152-preliminary-freeze-r1/review-freeze.json`, including sizes and SHA-256, and makes a byte-identical private `frozen/` copy. `freeze-before.json` and `freeze-after.json` record the before/after verification of originals and copies. Candidate scripts were read as evidence, never executed or imported. The independent checker was written here from scratch. Root's reported replay is background only.

I read ancestor `openai-proof-research/AGENTS.md`, batch `AGENTS.md`, relevant ledger and prior-campaign context, and the frozen source/disposition/history/provenance records. The exclusion of routine corollaries is the governing eligibility rule. Root alone adjudicates; the supplied 9 additional/39 total/next 40 context remains untouched.

## Source fidelity and dependency scope

The inspected primary body is Adel P. Kazemi, *Total Dominator Coloring of the Hypercube Q_(2^n)*, Contributions to Mathematics 13 (2026), 1–10, DOI 10.47443/cm.2025.102, publisher URL `https://shahindp.com/Contrib_Math/v13/CM26_v13_pp1-10.pdf`. Frozen `sources/kazemi.txt` retains page boundaries and superscript placement from that PDF. Page 10, Conjecture 6.1, is exactly the all-integer-n>=2 assertion

    chi_td(Q_(2^n+1)) = 2^(2^n-n+1) + 2.

Here d=2^n+1, V=2^d, and 2^(2^n-n+1)=2^(d-n)=V/(d-1). This is not dimension 2n+1. At n=2 it says chi_td(Q5)=10, using gamma_t(Q5)=8. The source's Question 6.1 on well-total domination is distinct. Definition 2.1 on p.2 uses a proper coloring and the vertex-first condition: for every vertex there exists a color class all of whose vertices are adjacent to it. No single class need dominate every vertex; vertices of the class themselves do not dominate it in a loopless graph.

On p.9 Fact 5.1(1) says the common neighborhoods cover the vertex set. Parts (2)–(6) give: two distinct vertices with a common neighbor have exactly two common neighbors; a class larger than d has no common neighbor; a class of at least three vertices has at most one; a singleton has d. Part (7) sums coverage using class-size counts. Its displayed assumption is a minimal TD-coloring; all the local statements used here have direct proofs for arbitrary nonempty classes, so no minimality assumption is smuggled into the candidate. Theorem 5.1 is for dimensions 2^n, n>=3, not 2^n+1. Its displayed counting proof divides by the size of the largest class. I do not invoke its conclusion or import its ordered-size assertions into the present proof.

The 2017 dependency actually inspected is Azarija–Henning–Klavzar, *(Total) Domination in Prisms*, EJC 24(1), #P1.19, published February 3, 2017, retained author-hosted body `https://users.fmf.uni-lj.si/klavzar/preprints/Electronic_JC_Azarija_Henning_Klavzar_2017.pdf`. Theorem 1 (p.2, proof pp.5–6) says gamma_t(G square K2)=2 gamma(G) for bipartite G. Its proof uses two isomorphic open-neighborhood hypergraph components, then Claims 9–11 give gamma_t=2 tau, gamma_t<=2 gamma, gamma<=tau. Theorem 3 (p.3) records gamma(Q_(2^k))=2^(2^k-k) for k>=1. Corollaries 12 and 13 (p.6) explicitly yield gamma_t(Q_(2^k+1))=2^(2^k-k+1). Thus gamma_t(Q_d)=g=V/(d-1) has exactly the required scope. This body does not prove the TD-coloring equality. The original van Wee and Harary–Livingston bodies underlying Theorem 3 remain unread here; the actual published 2017 theorem is the explicit dependency, not an independently reconstructed proof of those upstream results.

## Independent full mathematical derivation

Fix n>=2 and d=2^n+1>=5. A proper coloring is represented by its nonempty classes C, which partition all V vertices. Empty colors are discarded; otherwise an empty class would vacuously satisfy the TD condition and invalidate the problem's definition.

For a nonempty C let CN(C) be the intersection of its open neighborhoods. Call C active if CN(C) is nonempty, with a active classes and t other classes. The literal TD quantifiers imply that the union of CN(C) over active classes is the whole cube. Choosing one representative from every active class gives distinct representatives, since the classes are disjoint. Each vertex sees the representative of any class it totally dominates, including when that vertex is itself among the chosen representatives (it must then see a representative of a different class). They form a total dominating set. Consequently a>=gamma_t(Q_d)=g. This is total domination, not merely domination of vertices outside the chosen set.

For every active class,

    |C| + |CN(C)| <= d+1.                                      (A)

If |C|=1 this is 1+d. If |C|=2 there are exactly two common neighbors, so the sum is 4<=d+1. For |C|>=3, membership in the neighborhood of any common neighbor gives |C|<=d. If there were two common neighbors u,w, then C would lie in N(u) intersect N(w). Two distinct cube vertices have at most two common neighbors: adjacency to a shared vertex forces distance two between them, with just the two ways of undoing one of the two differing coordinates. This contradicts |C|>=3. Hence |CN(C)|<=1. These arguments require neither a preferred color ordering nor a restriction on how many vertices a class covers privately. Overlap between common neighborhoods only weakens the needed coverage lower bound.

Every independent set S has size at most V/2 by the perfect matching obtained by flipping a fixed coordinate. If equality holds, the d|S|=dV/2 edges incident to S account for all cube edges, since independence prevents double counting. Thus its complement is independent too. The cube is connected (successively flip differing bits); its bipartition is unique up to exchange, so S is a parity part. This last assertion can also be seen by alternating membership along every edge starting at one vertex.

An inactive color class cannot have size V/2. For if it were a parity part S, every other nonempty class would lie in the opposite parity part. Its common neighborhood is contained in S, while CN(S) is empty by inactivity. All vertices outside S would remain uncovered. Thus each inactive class has size at most V/2-1. At d=5 the strict one-vertex loss here is essential; replacing it by the ordinary independence bound would not finish that endpoint.

Suppose there are at most g+1 nonempty classes. Since a>=g, t is either zero or one.

* If t=1, then a<=g and the active classes contain at least V/2+1 vertices. Summing (A), and separately using common-neighborhood coverage, gives (d+1)a >= V/2+1+V. But

      3V/2+1-(d+1)g = V(d-5)/(2(d-1))+1 > 0.

  This contradicts a<=g. At d=5 the margin is exactly 1, not zero.
* If t=0, the active classes contain all V vertices, so (d+1)a>=2V. On the other hand a<=g+1, and

      2V-(d+1)(g+1) = V(d-3)/(d-1)-(d+1)
                         >= V/2-(d+1) > 0.

  The first inequality uses d>=5. The last follows from 2^(d-1)>d+1: at d=5 it is 16>6, and increasing d by one doubles the left side while adding only one to the right. Thus this case also contradicts the class budget.

Therefore chi_td>=g+2 for every required n, without an induction on sample dimensions. Conversely, take a minimum total dominating set D, give its g vertices distinct singleton colors, and use two fresh parity colors for vertices outside D, omitting empty residual classes. All classes are independent. Every vertex has a neighbor in D and hence totally dominates a singleton class, even vertices in D. This gives at most g+2 classes. The lower bound forces equality. The exponent and boundary match the literal published conjecture. I found no mathematical gap or counterexample to this derivation conditional on the stated known gamma_t value.

## Independently designed bounded checks

`independent_check.py` uses integer bitsets, with no candidate imports or symmetry-class shortcuts. It exhausts **all independent subsets** of Q3, Q4 and Q5, rather than just subsets of one neighborhood: respectively 34, 742, 254474 nonempty sets. It computes actual common neighborhoods, checks (A) for every active set, and checks the exact maximum independent sets. The only maxima are the two parity parts in every tested dimension. Active counts are 28, 144 and 704; no weighted violations occurred.

It separately enumerates all 354 canonical proper partitions of Q3, tests the literal vertex-first TD condition on every vertex and every class, and finds 266 TD partitions and minimum four classes. For every TD partition it directly tests the representative total-dominating set and the strict inactive-size bound. Q3 is a boundary control outside n>=2, and indeed does not have gamma_t+2 colors.

For Q5 it independently computes gamma_t through exact subset covering on both parity sides. On each side all subsets of sizes 0,1,2,3 (1,16,120,560 subsets) fail to cover the opposite parity part; among all 1820 four-subsets, 40 cover it. Thus gamma_t(Q5)=4+4=8 without appealing to the source formula at that endpoint. Two witnesses give an explicit ten-class TD-coloring; nonemptiness, disjointness, full vertex partition, properness, and the vertex-first TD quantifier are checked directly. Exact integer margins are also tested at n=2 through 8, giving margins (1,10) at n=2. These finite experiments support and debug the ordinary argument; they do not replace any universal step, and they do not enumerate all Q5 colorings.

Both guarded executions succeeded without a cap increase. `independent-run.log` records exit 0, sampled peak group RSS 11849728 bytes, approximately 0.361 seconds; the preparation log records 9740288 bytes. Sampling is nominally 40 ms and can miss transients; no assertion of continuously measured peak RSS or exact scheduling is made. No failed experiment or failed retrieval was discarded; this review made no new retrieval attempts.

## Adversarial eligibility adjudication

The strongest case **against exclusion** is real: the inspected published text deliberately states the target as a conjecture; neither Fact 5.1(7) nor Theorem 5.1 explicitly gives the weighted sum (A), the active-class representative reduction, or the strict inactive-size equality argument. Coverage alone only counts CN(C), and the displayed source proof treats a different dimension regime. Therefore it would be false to describe the whole theorem as already proved in those bodies, or as a mere substitution n -> n+1 into Theorem 5.1. Shortness and elementary ingredients alone are not valid exclusion criteria. The weighted combination is new reasoning relative to the inspected exposition, and the d=5 strictness must be earned.

Nevertheless, my independent recommendation is exclusion under this campaign's unusually strict routine-adaptation rule. The **complete bridge**, with every extra step exposed, is:

1. Repackage Fact 5.1(2)–(6)'s class-size/common-neighbor table as its immediate linear bound |C|+|CN(C)|<=d+1. There is no additional cube-structural claim in that repackaging.
2. Use Fact 5.1(1)'s exact coverage, together with choosing one vertex from every class which covers something, to apply the already known gamma_t lower bound. This leaves at most one noncovering class under the tested color budget.
3. Use the elementary equality case of the already recalled bound alpha(Q_d)=V/2 to remove one vertex from the allowed size of that noncovering class. The proof needs only regularity and connected bipartiteness.
4. Add the partition-size count to the coverage count with coefficient one, substitute the known g, and compare the two displayed scalar margins.

This is a finite table compression, elementary representative selection, a standard extremal equality case, and two positive linear combinations of the source counting constraints. It does not develop a new domination construction, a new total-domination bound, a new classification of cube colorings, or a hard additional structural lemma. This explicit bridge is why I judge it a routine extension of the source machinery, rather than adopting the candidate's self-description. The fact that a source author left the consequence conjectural is relevant evidence against casual dismissal, but does not by itself establish substantive work under the stated standard.

This remains a judgment about the bridge's substance, not a theorem that the bridge was historically routine or previously published. Root could reasonably set a more permissive threshold and decide to investigate. The strongest falsifier of my exclusion recommendation would be a demonstrated nonroutine missing lemma in steps 1–4, or a campaign-consistent reason that inventing this simultaneous size/coverage count and extracting the strict equality case crosses the substantive threshold despite the explicit elementary bridge. No such mathematical missing lemma survived this review. Finding an earlier actual body proving the full target would instead strengthen exclusion for a different reason; no such body is claimed here.

## Novelty limits and formal feasibility

The frozen 2013 Open Problem Garden body concerns all d>=5 with value 2^(d-2)+2; its 2014 refutation comment is not a proof of the much smaller 2026 target. In particular at d=9 that old expression is 130, while the present target is 66. The frozen Omega `Hypercube.md` body proves regularity and edge count; `HypercubeInequality.md` is a determinant/facet-sum inequality. Neither inspected body states a TD-coloring theorem. The fixed Omega head is 490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c and the fixed OpenAI head is 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Both inherited 300-path comparison intervals remain capped. The fixed Library path screen, historical role index and lexical no-hit reports are bounded evidence, not full body audits; I did not independently re-open all historical original paths. No HEAD chasing occurred.

Closest unread actual bodies remain Harary–Livingston 1993, original van Wee bounds, Kazemi 2014 product coloring, and Henning 2015 TD-coloring; registry path hits other than the two inspected bodies also remain semantically uncleared. No worldwide priority, current registry completeness, exhaustive citation search, or prior full-proof absence is asserted. This review does not authorize significant further investment without the campaign's current-source gate; it recommends stopping on eligibility first. No 403/429 was retried.

Formal feasibility appears plausible for the finite graph/counting bridge, but no Lean was written or run. A literal endpoint would still need all-n cube common-neighbor lemmas, finite nonempty partitions with exact TD quantifiers, the independent-set equality argument, representative cardinality and domination, and the exact known all-n gamma_t dependency proved or linked to an allowed certificate. Merely inserting that dependency as an axiom would not meet the campaign's final standard. There is no formal PASS or claim that an existing library already contains these bridges.

The strongest mathematical falsifiers are: a nonempty active class violating (A), a non-parity independent set of size V/2, a parity-sized inactive class in a valid TD partition, or a failure of the cited all-n gamma_t formula. The ordinary derivation disposes of the first three; the fourth is explicitly the known source dependency. Recommendation remains **EXCLUDE / retain as an uncredited ordinary source bridge**, with root alone responsible for disposition.
