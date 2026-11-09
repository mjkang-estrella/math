# Full ordinary proposal: MathDB 360614
AUTHOR ONLY. No independent PASS, novelty clearance, significance qualification, formal execution, dispatch, acceptance or credit. Scientific HOLD recommended. This file preserves a complete printed-scope refutation for root adjudication, not a qualified significant discovery.

## Literal and source
The immutable literal is in literals/360614.jsonl with exact provenance in literal-provenance.json. It asserts, for every k>=3 and every fixed finite graph H with chi(H)<=k, both rex(n,H,K_(k+1))=(1+o(1))N(H,T(n,k)) and eventual exact equality on k-divisible n. N counts non-induced subgraph copies, not induced copies. Source: Gerbner and Hama Karim, Generalized regular Turan numbers, arXiv2311.01579 downloaded v2 (28 August 2026), p3 Conjecture1.5; journal AJC90(3)(2024)326–340 p328 Conjecture1.5. Both actual bodies state chi(H)<=k. Definition of rex and N read on original p1 and journal326–327. Proposition1.6 is only for complete k-partite H, with positive sizes in its proof. No maximum-degree or maximal-edge-count requirement on the regular host occurs. The journal proof of Proposition1.6 was compared through the corresponding original proof; it does not settle bipartite H when k=3. No final equivalence of the two entire manuscripts claimed. Material text extraction read; visual glyph inspection remains unpaid.

## Construction and full proof
Fix H=K_(12,12), k=3, and any integer m>=176. Set n=6m. Let B_m=K_(3m,3m). It is simple, n-vertex, 3m-regular, and bipartite, hence K4-free. H has chromatic number2<=3. Let Q_m=T(6m,3)=K_(2m,2m,2m).
For a graph G write I(H,G) for the number of injective maps of the fixed labelled V(H) into V(G) sending edges to edges. Then N(H,G)=I(H,G)/|Aut(H)|. The action by precomposition is free, and its orbits are exactly subgraph copies (extra ambient edges do not matter). Here |Aut(H)|=2(12!)^2: the two parts are the unique independent color classes in the connected complete bipartite graph, and may be permuted internally or interchanged.

Exactly I(H,B_m)=2*((3m)_12)^2, where (a)_12=a(a-1)...(a-11). Connectedness forces the two H-parts into distinct host parts, and those choices are sufficient.

For an upper bound on I(H,Q_m), allow arbitrary, possibly noninjective homomorphisms. All colors used on one part of H must be disjoint from all colors used on the other. There are three host colors. Either both parts use one color: 6 choices, each with (2m)^24 maps. Or one part uses one color and the other both remaining colors: 2*3 choices, each with (2m)^12*((4m)^12-2*(2m)^12) maps. This exhausts the disjoint nonempty color supports. Hence
I(H,Q_m)<=6*(2^12-1)*(2m)^24 <6*2^12*(2m)^24.

For numbers a_j in [0,1], product_j(1-a_j)>=1-sum_j a_j, by induction (the two-factor difference is a_1*a_2>=0). Apply to two copies of j/(3m), j=0,...,11. The sum is 2*(0+...+11)/(3m)=44/m. Thus
((3m)_12)^2 >=(3m)^24*(1-44/m)>=(3/4)*(3m)^24,
and I(H,B_m)>=(3/2)*(3m)^24.
The exact integer inequality 3^12=531441>524288=2^19 implies 3^24>2^38. Consequently
(3/2)*3^24 >6*2^36,
so I(H,B_m)>I(H,Q_m), hence N(H,B_m)>N(H,Q_m) for EVERY m>=176. Since rex is at least N(H,B_m), eventual exact equality fails on arbitrarily large 3-divisible n.

There is also a fixed relative gap. Indeed
I(H,B_m)/I(H,Q_m) > 3^24/2^38 >1
for every m>=176, by the same inequalities. Division is legitimate: Q_m contains H (choose12 vertices from each of two parts). Thus the ratio rex/N cannot tend to1 even along n=6m, refuting the first clause as well. This is a full negation of the printed universal conjunction; no claim is made about chi(H)=k, connected hosts of prescribed maximum degree, or exact determination of rex.

All arithmetic and proof performed personally; no enumeration, numerical test, CAS, solver or formal tool was used.

## Adversarial significance investigation
First shortcut: regularize the source's irregular C5-blowup example by adding vertices. This fails quantitatively: degree balancing changes the leading H-copy density and cannot be treated as negligible.
Second route: compare regular balanced complete multipartite hosts directly. For general s, H=K_(s,s), T(n,2) gives leading labelled density2/2^(2s), while T(n,3) gives6*(2^s-1)/3^(2s). Their ratio is (9/4)^s/[3*(2^s-1)], exceeding1 for large s. The explicit s12 proof above pays injectivity and finite thresholds rather than relying only on leading terms.
Third route: repair the assertion to chi(H)=k, for example by attaching or joining a triangle. This is NOT established: the bipartite host contains no triangle, and joining an apex makes H complete3-partite, a source-proved case. No stronger corrected-scope counterexample is claimed.

The strongest adverse case is substantial: this is an elementary fewer-parts comparison in classical generalized Turan counting, and may be adjudicated as correcting the overly broad chi(H)<=k domain. It introduces no new extremal invariant or classification, and does not settle a new positive regime. Under the user's instruction, this lane moved on to inversion and crossing targets instead of investing in formalization. The strongest positive case is equally explicit: the final journal deliberately prints the broad range, explicitly motivates absence of ANY regular counterexample, and the family refutes BOTH asymptotic and exact claims with ordinary connected regular hosts, rather than exploiting a small-order endpoint. Smallness or familiar tools alone are not an authenticated routine-prior reduction.

Actual prior-body check: full acquired2205.13455v1, Grzesik–Gyori–Salia–Tompkins, read all6pages. Theorem1's all-r counterexamples use highly unequal powers-of-cycles blowups; their proof is not regular, and does not supply this balanced-host comparison. Theorem2 concerns triangle-free hosts, not all K4-free hosts. A complete applicable earlier-result-to-target exclusion has NOT been authenticated. This is a bounded nonmatch, not new-to-literature certification. Actual cited1991 Gyori–Pach–Simonovits proof and Turan-good literature remain unread; no specific theorem from them is imported.

Three native searches/nine exact strings are retained with precharges and full responses. No matching exact published refutation was authenticated. Four inherited registry-root artifacts and the AI index are closed; none was retried or indirectly reconstructed. Unsolicited registry/mirror search hits are retained as navigation only, never used as current-head or proof clearance. No worldwide novelty claim. Root alone decides whether the positive case survives the domain-correction/routine objection; until then this proposal is unqualified and must not be dispatched.
