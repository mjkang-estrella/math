# Exact finite-exception interface and remaining representation problem

Author work, not independent review. Full target remains scope-freeze.md, with no regularity assumption on the automorphism. The following conditional calculation is support only and is not nominated separately.

## 1. Surviving joins are actual joins

Let E be finite and P=D_T\E. For a,b in P, if j=a∨b belongs to P, it is their least upper bound in P. Conversely, if a,b have a least upper bound c in P, then c=j in the full degrees. Otherwise j<c. Choose representatives J,C of j,c. Category cone avoidance relative to J gives a real G with C not computable from J⊕G. We can also require deg(J⊕G) outside E: for any e in E, equality to e implies G≤_T e, and the reals computable from one degree form a countable, hence meager, set. Thus d=deg(J⊕G) is an upper bound of a,b in P with c not≤d, a contradiction. (The source's two-real category lemma supplies G as the join of its two auxiliary cuts; the same countability avoidance works.)

Every order automorphism π of P consequently preserves every join which exists in P, as an actual full-degree join. This does not define π at a deleted degree.

## 2. What a Borel lift would buy

Assume provisionally that π and π^{-1} each have Borel representatives on sets whose degrees are in P. This additional premise is NOT in the frozen target and is not supplied by the pinned representation theorem.

The forbidden real cuts B={x:d(x)∈E} form a countable Borel set. Composing a representative with the rational-cut map defines F on R\B. Set F(x)=the empty set on B. The resulting total map is Borel with countable fibers: outside B each fiber lies in one input degree by injectivity of π, and adding B preserves countability.

Let B_down={x:d(x)≤e for some e∈E}; this too is countable. On the comeager Borel subset Ω of R² where x,y are outside B_down and x+y is outside B, the addition inequality

    F(x+y) ≤_T F(x) ⊕ F(y)

holds. Indeed j=d(x)∨d(y) cannot belong to E because x∉B_down. Its image is the actual join of the two image degrees by §1; monotonicity applies to x+y because its degree remains in P. The complement of Ω is a countable union of vertical, horizontal, and diagonal lines.

Define e(x,y) to be the least successful addition index on Ω, and zero elsewhere. The successful-index relation is Borel; hence this is a total Borel function. Choose a comeager continuity restriction for e and intersect it with Ω. Choose a comeager continuity restriction D for F as in source lem:continuity. For a fixed irrational t, put H=Q+Qt. Require

    u+s∈D,
    (u+s,v−u+a)∈E_good,
    (v+s,u−v)∈E_good          for all s,a∈H.

This is comeager: the last two affine maps of (u,v) are homeomorphisms, and the first is a translated coordinate projection. Every addition actually used below therefore lies in Ω, not merely almost every addition.

At a chosen good pair, relative continuity gives fixed successful program indices p,q near (u,v−u) and (v,u−v), with radius ρ<1. Countable fibers and continuity of F|D give two offsets b_-<0<b_+ in (−ρ,ρ) with distinct tested output bit, and a rational δ>0 with 3δ<b_+−b_-, δ<ρ, on which that bit points inward at the endpoints. This is precisely the choice justified by the source recovery proof and uses no assertion at a forbidden addition pair.

Starting s_0=0, let r_n be the tested bit comparison and s_(n+1)=s_n+δ(t−r_n). The endpoint conditions keep s_n∈H∩[b_-,b_+]. The fixed four oracles F(u), F(u−v), F(v−u+δt), F(v−u+δ(t−1)) compute all r_n: p computes F(v+s_(n+1)) from the current F(u+s_n) and the chosen increment oracle, then q computes F(u+s_(n+1)) using F(u−v). Each call is valid by the all-shifts condition, and finite-depth substitution terminates. Summation gives |t−N^{-1}Σr_n|<1/(Nδ), so these four oracles compute C(t).

In addition require the four affine arguments to avoid B and b=d(t)∨d(u)∨d(v) to avoid E. All four argument conditions, simultaneously for every rational δ, remove countably many lines. The condition on b follows by choosing u outside B_down. Thus these restrictions remain comeager. When d(t)∈P, all four output degrees are ≤π(b), so d(t)≤π(b), and applying π^{-1} gives π^{-1}(d(t))≤b. Category avoidance, with t and one representative of π^{-1}(d(t)) fixed before u,v vary, yields π^{-1}(d(t))≤d(t). Applying the argument to the provisionally Borel-representable inverse yields equality. If 0∈P it is the unique least element and is fixed; every other degree is represented by an irrational t.

Conclusion: Borel representatives for both directions would close the full degree-by-degree argument. The countable-exception repair is a direct adaptation of the paid source recurrence, not by itself a substantial new nominee. The arbitrary-automorphism representation bridge remains unpaid.

## 3. Why elementary completion does not yet restore the holes

A deleted degree a can be a join of surviving degrees, in which case a missing join is visible as such. This does not cover all holes. If a is a minimal nonzero degree and 0 survives, every surviving degree strictly below a is 0; its lower trace therefore agrees with that of 0. A completion constructed only from lower traces cannot distinguish them. More generally a strong minimal cover can have the same surviving lower trace as its predecessor. These are explanations of a proposed reconstruction method's missing information, not nontrivial automorphisms of a punctured degree order.

Likewise, in the full order one may express a as the meet of suitable larger degrees. After deleting a, that meet may collapse to 0 in the minimal-degree case. An automorphism of P preserves the meet computed in P, not the deleted meet. One must not silently use the full-order coding or meet interpretation in P.

A possible remaining route is to work on full upper cones above all holes, prove an arithmetic representation for the induced isomorphism between two (possibly different-base) cones, and then recover lower degrees by coding. A self-automorphism theorem for one relativized cone is not automatically a representation theorem for an isomorphism between different cones. This route is under investigation; no such theorem is asserted here.

## 4. Actual antichain-coding route

The 2005 primary Lemma3.1.7 is more useful than a black-box full-order representation theorem. It constructs g0,g1 so that each coded antichain member a has a common lower bound of g0∨a and g1∨a not below a; conversely, every y below the specified bound admitting such a witness lies above a coded antichain member. The code takes minimal such y.

Here is the exact deletion-stability statement, independent of any forcing claim. Suppose A⊂P is an antichain, b,g0,g1∈P, g0 and g1 are not below any member of E, and:

1. For each a∈A there are infinitely many distinct degrees z≤g0∨a,g1∨a with z not≤a.
2. For every y≤b, if such a common-lower-bound witness exists in the full degrees, some a∈A satisfies a≤y.

Then the same minimal-witness formula, evaluated in P, defines exactly A. All joins g_i∨y survive because g_i is not below E. At a∈A, one of the infinitely many witnesses survives finite deletion. A false extra minimal y in P would satisfy the full-order property, hence lie above an a∈A which still satisfies the formula in P. Minimality forces y=a. This is a full proof of the conditional deletion-stability lemma.

The primary forcing uses a shared column C(k) computable from either G_i⊕A_k and noncomputable from A_k. A plausible strengthening divides that shared column into infinitely many disjoint infinite subsequences, chosen using A_k's enumeration of its own introreducible coding positions. Requiring the resulting subsequences to be mutually Cohen generic over A_k would give infinitely many distinct joined witnesses A_k⊕C(k,j), all lying below both G_i⊕A_k. For each finite condition and finite desired values of these shared bits beyond its support, one can extend both coordinates with those same values, so the projection onto any finite set of shared subsequences has the required finite-extension freedom. Individual G_i coordinates likewise have arbitrary finite-extension freedom and can avoid the downcones of E by genericity relative to representatives of E.

This establishes why witness replication is plausible and identifies the exact requirements. It is NOT yet a verification of the effective finite-injury construction in primary Theorem3.2.2: that construction sometimes drops higher restraints, and one must prove the shared subsequences remain correctly readable after each final injury and that all new diagonal requirements fit the same arithmetic bound. The qualitative forcing construction and the finite-injury effective construction must not be conflated.

The general-relation coding reduction (primary Lemma3.1.11 and Theorem3.1.2) uses independent generic tags c(x) and antichains x∨c(x). Choosing the tags generic relative to an upper bound on the relation and E keeps all those tag and join degrees outside E. This would transfer the robust antichain statement to countable relations on P. But the full target additionally needs controlled effective coding and decoding, persistent extensions of automorphisms of punctured ideals, and the generic-extension representation argument. No blanket 'same proof' claim is made for these obligations.

The primary Theorem3.1.15 is an explicit warning: a cofinal elementary substructure of the full Turing degrees is the entire structure. Every proper finite puncture is cofinal, so it cannot simply be declared elementary in the full order. This rules out that particular shortcut, not the frozen rigidity statement.
