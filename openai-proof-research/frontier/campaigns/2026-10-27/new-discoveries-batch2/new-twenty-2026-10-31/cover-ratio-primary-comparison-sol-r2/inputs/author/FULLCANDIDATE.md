# Ordinary proposals only — no qualified survivor or acceptance

Four literal endpoints have ordinary refutation arguments below. These are not four claimed new results: the two scoring endpoints share one simple two-component mechanism. Independent fidelity/significance review, current applicable registry body review, formal execution and acceptance are absent. Broad family reconciliation was late for cover cost and regular MIS; procedural HOLD is preserved. All original literals and provenance are in literals/ and literal-provenance.json. No mathematical computation was executed.

## 323064: positive scoring selective-sum counterexample

Primary: Stewart, arXiv1202.4656v1, Definitions1.6–1.7 and3.1–3.2, Conjecture3.3 (pp4,8,11–12). A finite octal game with sole digit3 permits removal of one bean, leaving either one nonempty heap or no heap. Scores are arbitrary real numbers in Definition1.6. Conjecture3.3 explicitly says two finite octal games; the score-equals-number-removed restrictions of Conjecture3.2 are not repeated in3.3. Use O=(3,2), P=(3,1), fix the P heap at m=1, and vary n>=0 in O. Both games are taking-no-breaking, with strictly positive integer scores. No splitting/order ambiguity occurs.

Let U(n) be the value of the lone O heap. U(0)=0, U(n)=2-U(n-1), so U(n)=0 for even n and2 for odd n. Let D(n) be the disjunctive value with the one-bean P heap. D(0)=1. For n>=1 the entire move set is exactly: remove one from O and gain2, or remove the P bean and gain1. Thus
D(n)=max(2-D(n-1),1-U(n)).
If D(n-1)=1 then the first alternative is1, while the second is1 for even n and-1 for odd n. Induction proves D(n)=1 for every n. In particular its least positive eventual period is1.

For selective play write S(n); S(0)=1. Its entire move set has the previous two alternatives and the simultaneous move gaining3:
S(n)=max(2-S(n-1),1-U(n),3-U(n-1)).
For odd n, the inductive preceding value is1, U(n)=2,U(n-1)=0, so the three alternatives are1,-1,3, hence S(n)=3. For even positive n they are-1,1,1, hence S(n)=1. This proves S(2j)=1 and S(2j+1)=3 for every j. Given any proposed eventual threshold N, an even n>=N has S(n+1)!=S(n); period1 fails. The premise holds with p=1 and the conclusion fails. This is a negation of the full universal literal, not merely a parameter case in support of it.

Failed shortcut: assuming all operators preserve period because the individual heap values do is invalid: a disjunctive option can flatten an alternating sequence. Taking both component scores equal gives D alternating and does not refute the premise/conclusion implication; tuning2:1 produces the constant premise. Positive scores remove a possible zero-score objection for this endpoint.

Significance and complete routine-adaptation concern: source Theorem3.4 already gives selective additivity when all individual values are nonnegative. Here U is0/2 and the P value1, so that theorem gives S=U+1. Together with the elementary disjunctive induction above this is a COMPLETE applicable source-theorem-to-target counterexample bridge. The strongest contrary significance case is that the source explicitly conjectures period preservation for this broader domain even immediately after that theorem, and the witness refutes an infinite eventual claim using legal positive scores, rather than exploiting malformed syntax or finite transient values. Do not infer routine status merely from shortness, but do present this bridge to root adjudication. No significance clearance is claimed.

## 323065: sequential-join counterexample

Use O=(3,0), P=(3,1), m=1. Zero is a real score expressly allowed by Definition1.6. The target is Conjecture4.1, not the narrower score-equals-beans conjecture1.1. The lone O value U(n)=0 for every n. The disjunctive sequence has D(0)=1 and D(n)=max(-D(n-1),1)=1 by induction. It has least positive eventual period1.

Use the source's numerical sequential recurrence Definition4.2, pp14–15: play O until exhausted, then P. For J(n), J(0)=1 and J(n)=-J(n-1), hence J(2j)=1,J(2j+1)=-1. Every threshold has a later even/odd unequal adjacent pair. This refutes period1 preservation. Even if the general displayed Definition4.1 were read as inserting one switching move, this would reverse all signs without removing perpetual parity; nevertheless the proposed literal bridge is Definition4.2, whose numerical recurrence is explicit. Its earlier general terminal display is awkward/self-referential and warrants independent fidelity review. Our taking-no-breaking witness avoids the source's acknowledged unspecified order after splitting.

Failed routes: with forced one-bean moves of positive score a in O and score b in P, disjunctive values alternate b,|a-b|, while sequential values alternate b,a-b. If b=a/2, both are constant. Thus the positive2:1 selective witness does not also refute the sequential statement. Zero-score moves are essential to THIS sequential witness; no all-positive sequential counterexample is claimed. The parity argument is exact for every n, not an enumerated table.

Prior/significance: Definitions1.6/1.7/4.2 give a complete direct derivation. No read theorem explicitly claims this refutation. The 2017 Games of No Chance5 companion Definitions30–31, Theorem32 and Sections5.1–5.3 allow arbitrary real scores; Conjecture35 concerns score-equals-removal, and its printed O=(3333,2222) discussion refutes a different proposed period2k generalization, not the two-operator preservation implication. No identification with that public example is asserted. This distinction still needs independent comparison and significance adjudication. Both scoring proposals are one closely related family for any future counting decision.

## 323710: 320-vertex path-to-clique counterexample

Primary: Georgakopoulos, A Tractable Variant of Cover Time, arXiv1206.6605v1, Definition1.1, equation(1), Proposition2.1 and Conjecture5.4. Write N=|V|-1. Source lowercase cc_r=(1/N)sum_v H_r(v); CT_r is expected time to first visit all vertices, without return to root. The literal varies graph with fixed vertex count, so multiplication by N would not change which graph maximizes the ratio. We retain the actual lowercase normalization.

Construct a simple connected undirected graph B(L,m): start with path0,1,...,L, identify L with a vertex v of K_m, add no other edges. Root0. It has L+m vertices. Take L=64,m=256, giving320 vertices and N=319.

All expectations used below are finite: on any connected finite graph, from any vertex there is a walk of bounded length visiting any prescribed vertex (or all vertices), with probability bounded below by a fixed positive number. Successive blocks therefore give a geometric tail for the hitting/cover times. First-step equations and nonnegative summation/tower arguments are justified. No limit-of-computation assumption occurs.

Before first hitting v, the walk is the reflected path walk. The expected hitting function h_i=L^2-i^2 satisfies h_L=0,h_0=1+h_1 and h_i=1+(h_{i-1}+h_{i+1})/2 for0<i<L. Uniqueness follows by the discrete maximum principle (a harmonic difference achieving a nonzero interior extremum propagates to absorbing L). Hence E_0 T_v=L^2. In particular every one of the m-1 other clique vertices has H_0(w)>=L^2. Consequently cc_0(B)>=(m-1)L^2/(L+m-1).

After first reaching v, the entire path has been visited. Suppress excursions from v into the tail, recording only transitions between different clique vertices. From v each trial chooses one of m neighbors; the tail neighbor has probability1/m and its mean return time to v is2L-1, by the same h_i formula at i=L-1. Let a be the expected duration until the next different clique vertex when starting at v. First-step conditioning gives
 a=(m-1)/m + (1/m)(2L+a),
so a=1+2L/(m-1). The successful clique neighbor is uniform among m-1 choices; all other clique vertices take exactly one step per embedded transition. Thus the embedded walk is simple random walk on K_m and every embedded transition has conditional expected physical duration at most a.

If k clique vertices remain unvisited, each embedded step hits one with conditional probability k/(m-1), since the current vertex is already visited. The waiting time has expectation(m-1)/k: induct on survival steps, or solve e=1+(1-k/(m-1))e. Summing stages gives (m-1)H_{m-1} expected embedded steps. Conditioning on the history before each transition and summing its expected duration therefore bounds the physical clique-cover time by a(m-1)H_{m-1}=(m-1+2L)H_{m-1}. It follows that
 CT_0(B)<=L^2+(m-1+2L)H_{m-1}.
No electrical-network formula, Matthews theorem, or independent-trials assumption is needed.

For m=256, partition1,...,255 into blocks [2^j,2^{j+1}-1],0<=j<=7. Each block contributes at most1 to H255, so H255<=8. Since255/319>3/4, cc_0(B)>3*4096/4=3072. Since383<384,
 CT_0(B)<4096+384*8=7168.
Thus cc_0(B)/CT_0(B)>3072/7168=3/7.

For the endpoint-rooted path on320 vertices put n=319 edges. H_0(i)=i^2 as above, CT=n^2 because reaching endpoint n covers the path, and sum_{i=1}^n i^2=n(n+1)(2n+1)/6. Hence its ratio is(n+1)(2n+1)/(6n^2). This is<3/8 whenever2n^2-24n-8>0, true for n>=16 since2n(n-12)-8>=120>0. Therefore the path ratio is<3/8<3/7<the B ratio. This proves a strict counterexample with equal vertex count and exactly the source's walk and normalization.

A full parameter route also survives: for L=t^2,m=t^3, the lower ratio bound is
 ((m-1)/(L+m-1)) * L^2/(L^2+(m-1+2L)H_{m-1}),
which tends to1, using elementary H_s<=1+log s. The universal upper bound cc<=CT follows from each hitting time<=cover time. This limit observation is not needed for the finite refutation and is not a separate credited result.

Failed mechanisms: rooted stars have early cheap discoveries but a long coupon tail, reducing the ratio. Endpoint paths have a spread of hitting times i^2, so their normalized ratio approaches1/3. A large clique rooted inside it likewise has coupon delay. Moving the root to a long tail makes the initial path-hitting delay common to almost every clique vertex, while that clique is still covered quickly thereafter. Crude bounding H_s by s loses the comparison; the eight dyadic blocks retain a rigorous finite certificate.

Prior/source scope: the actual companion1302.3212v2, introduction Theorems1–3, Section4.2 and Section5 text, concerns individual CC/RC/tree extrema and differing vertex preorders. It does not in the read passages prove the all-graph cc/CT ratio claim. Its clique-plus-star example distinguishes centrality orderings, rather than this path-to-clique ratio. Its actual2017 final body has not been read. The author publication page still labels1206.6605 Preprint2012; current version history for that source was not fetched. Current proof registries are not cleared by their rootheads/metadata. No worldwide novelty claim.

Significance: contrary routine case is that common initial hitting delay plus a complete-graph coupon bound uses standard elementary machinery and familiar lollipop geometry. Strongest significance case is a strict full-literal counterexample, with a ratio gap bounded by simple fractions and a family approaching the maximal possible ratio1, independently derived without a theorem giving the target conclusion. No read primary result-to-target bridge establishing routine adaptation was found for this proposal. Root must adjudicate; late broad-family reconciliation remains a procedural HOLD.

## 323059: regular-MIS finite counterexample, v1/literal only

Primary Ilinca–Kahn1202.4427v1, Section5 Conjecture5.2 explicitly displays the literal bound. The preceding paragraph has d congruent2 mod3 and divisibility by2(d-2); retain both. Take d=8,n=36 and G the disjoint union of four K9. Each vertex has exactly8 neighbors, 8 congruent2 mod3, and12 divides36. A maximal independent set contains exactly one vertex of each clique: independence allows at most one, and maximality forces at least one because otherwise any vertex of the missed component can be added. Independent choices across the four components give9^4=3^8 such sets. The conjectured upper bound is2^(36/12)*3^(36/6)=2^3*3^6. Since3^2=9>8=2^3, multiplying by positive3^6 gives3^8>2^3*3^6. This is a strict full-literal refutation, without any numerical enumeration or approximation of fractional powers.

The source's construction for d=8 instead joins two disjoint unions of two triangles. Its12-vertex component has18 maximal independent sets, leading at n36 to18^3=2^3*3^6, so the complete-clique witness genuinely exceeds that proposed construction. The source's asymptotic logarithmic Theorem1.2 is not contradicted: it is a d->infinity assertion, while this witness fixes d8.

Failed shortcuts: d2 makes the printed denominator vanish and would only expose an endpoint flaw; excluded. d5 unions of K6 attain equality and do not refute the bound. The d8 construction avoids both issues. No prior theorem is needed beyond an explicit combinatorial bijection. Smallness alone does not prove routine adaptation. Conversely, this could be a publicly known easy exception/corrected d-range: current targeted literature search for this late route was not performed because the3-call/9-query native budget was exhausted. The live arXiv page lists only v1 and no journal reference, but that is not a proof of no final/correction. Late broad-family reconciliation and lack of a full current body comparison are explicit HOLDs. No novelty/significance clearance or credit.
