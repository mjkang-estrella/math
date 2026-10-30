# Full-scope target and outcome

Outcome: UNRESOLVED, ZERO NOMINATION. This lane supplies no complete ordinary
resolution and no recommendation for Lean or manuscript investment.

Qi Chen, Ji-Ming Guo, Wen-Jun Li, Zhiwen Wang, *A conjecture on the
Nordhaus-Gaddum product type inequality for Laplacian eigenvalues of a graph*,
EJC32(4)(2025)#P4.37, published3November2025, DOI10.37236/14060,
actual publisher PDF pp1–3 and10–12. For EVERY finite simple undirected graph
G of order n>=2, arrange Laplacian eigenvalues in descending order
mu1>=...>=mun=0. Conjecture20 asserts, for EVERY integer
1<=k<=floor(3n/4), mu_k(G)mu_k(complement G)<=n(n-k).
Equality is asserted exactly when G or its complement is K_k joined to a
disconnected graph on n-k vertices having at least k+1 components.
No connectivity, regularity, integrality or cograph restriction may be added.
The full claim includes the equality classification; it is not resolved here.

## Source and early screens

Read ancestor/batch AGENTS, full ledger/prior-context JSON and current NEXT;
context-receipts.json binds bytes, counts and mutable context. Initial and exact
screen receipts preserve full matching original bodies, not snippets only.
Retained r133 index SHA256d794ec49...1cce51 has426515 aliases. First refresh
selected1630 original report paths,1136 distinct bodies,1596 unchanged and34
new/changed, no missing/oversized reports. Subsequent follow-up screen refreshed
1633 paths,1139 bodies. Original r111–r113 reports are individually retained.
Generated extraction/replay/input/packet roles are excluded explicitly, not by
entire lane or date. There is no global hit cutoff. This is a lexical screen,
not semantic or universal novelty clearance.

Omar domination-polynomial unimodality is old r70/r78: dropped. Boxed mesh
2609.13764, Kitaev–Qiu–Xu, is old r105: original full discovery disposition
reopened, including the mixed-occurrence obstruction and prior r71 duplicate.
No new theorem changes that gap; dropped. The initial tool output containing
the hit was truncated, and I downloaded redundant boxed-mesh bytes before
reading its disposition. This was a screening-order failure, not evidence of
freshness. The retained source has onlyv1 in observed arXiv history. No further
boxed research followed the reopened disposition. Late-growing permutation
search hits were not promoted or downloaded.

Exact title/ID/author/claim screens before the Laplacian and closest-source
downloads are history-exact.json and history-laplacian.json. Broad Li–Guo
matches include r54's DIFFERENT Filomat39(2025)4551–4564 square-energy
questions; that original disposition was reopened. No matching product claim
was located in the selected original report bodies. Generic surname and
Laplacian-product hits are not treated as substantive matches.

The current published main PDF is retained unchanged as primary bytes, not an
abstract surrogate. Theorem16 already proves k1, through its diameter cases
and resistance/Fiedler-vector argument. Theorem18 proves n/2<=k<=3n/4 by
the complementary-spectrum identity and the sum bound at n-k, then AM–GM.
Proposition19 gives counterexamples only ABOVE the conjectured range. Those
are not counterexamples to Conjecture20. Printed cross-reference numbers in
the final remarks drift; no correction to those numbers is nominated.

Closest source: Wen-Jun Li–Ji-Ming Guo, *Nordhaus-Gaddum type inequalities for
the kth largest Laplacian eigenvalues*, EJC31(1)(2024)#P1.31,
DOI10.37236/12008. Actual Theorem18/proof pp7–8 gives the Weyl sum bound for
k<=n/2 and a conditional middle-index consequence of Brouwer. It does not
state the new product bound. Its threshold, regular and multipartite cases
are special-family sum results, not the full product claim. Main-source k1
proof pp4–10 was also read in its actual body, with the small-n numerical
subargument distinguished from its general estimates.

Bounded public searches queried exact titles, authors, DOI and product/kth
claim aliases, plus follow-up terms on29October2026. Results returned the
two actual publisher bodies and adjacent spectral-radius/Brouwer papers.
No verified complete follow-up resolution was established. Search indexing
failure is not proof of absence; there is no exhaustive citer, MathSciNet,
zbMATH or worldwide priority audit. No claim that another conjecture's public
resolution automatically proves this one.

## Sustained mathematics: what is actually missing

Write a=mu_k(G), b=mu_(n-k)(G). The complementary eigenvalue is n-b.
The desired inequality is a(n-b)<=n(n-k). If a<=n-k it follows from b>=0.
If a>n-k it is exactly the nonlinear lower bound

    b >= n(a-n+k)/a.

The known sum question would only give a-b<=n-k, that is b>=a-n+k.
Since n/a>=1, this is weaker. Thus even a universal solution of the related
sum question alone does not discharge the product gap. For n/2<=k the source
already supplies a stronger sum upper bound and AM–GM; repeating it earns
no credit. The unresolved band is2<=k<n/2, across all graph structures.

An exact relaxation witness at n10,k2 has descending spectrum

    (9,9,6,6,5,4,4,1,0,0).

Removing one mandatory zero and applying x->10-x gives complement spectrum
(10,9,6,6,5,4,4,1,1,0). Both are nonnegative, bounded by10, with even
traces44 and46, summing to n(n-1). Every Brouwer prefix inequality on both
sides holds with m22 and23, respectively, as does every proposed sum
Nordhaus–Gaddum inequality. Yet their second eigenvalues give81>80.
Hence these scalar constraints alone cannot prove the product assertion.
This witness is not claimed to be a graph and is in fact nongraphical:
two zeros force exactly two connected components; eigenvalue9 forces one
component to have at least9 vertices. Their sizes must therefore be9 and1.
The order9 component has spectrum(9,9,6,6,5,4,4,1,0). Its internal
complement would have spectrum(8,5,5,4,3,3,0,0,0). Three components on
nine vertices have maximum component order7, impossible with eigenvalue8.
This uses only the classical bound that a component's Laplacian eigenvalues
are at most its order. It refutes a proof shortcut, not the source.

Another tempting sufficient statement, min(mu_k(G),mu_k(complement G))<=n-k,
already fails at C5,k2: both sides equal(5+sqrt5)/2>3. Their product is
(15+5sqrt5)/2<15, so the actual product bound survives. For blow-ups and
recursive constructions, the challenge is precisely to control the joint
large/small order statistics without replacing the graph by an arbitrary
positive semidefinite pair. No such universal mechanism was obtained.

Exact cograph construction uses sorted spectra. Disjoint union concatenates;
complement replaces one mandatory zero by0 and all remaining x by n-x.
Every cograph is recursively a union or join, so closure over all smaller
splits enumerates its possible spectra without claiming nonisomorphic graph
enumeration. Through order12 this yields37378 distinct spectra at the last
order, with all smaller levels retained in check-results.json. Five thousand
additional recursive samples have orders10..100, fixed seed142, repetitions
allowed. Across both pools683836 exact integer product comparisons have no
violation. Forty independently constructed adjacency Laplacians, orders1..10
four times each, verify their full characteristic polynomials by fraction-free
determinants at n+1 integer points. Four source Proposition19 controls above
the permitted range give positive excesses6,3,10,5. These verify conventions
and arithmetic only. Cographs omit induced P4 configurations and do not
exhaust arbitrary graphs. No all-cograph theorem, inequality classification
or new partial-case result is nominated.

## Registry chronology and limits

registry-retained.json reuses r133's read-only hash/path database to screen
historical registry-tree bodies, with exact missing/size limits and receipt
hashes. It is an inventory screen, not a proof-body audit. The qualified
latest inherited Omega point is a19a578cd06b57a4ea4d287cb0df92f9085117ae,
observed23:40–23:42UTC by r139; aa026→a19a returns six commits but300 paths
and is CAPPED. Earlier receipts keep their limits. OpenAI's qualified point
remains7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. No moving-head request,
full-current-tree claim or semantic registry clearance was made. Since no
full candidate survives, no target-specific current proof-body clearance was
attempted. A future full proof would require that gate and exact chronology.

## Objection, falsifier and disposition

Strongest objection: there is no universal proof, literal counterexample or
equality classification. All positive evidence is a restricted finite sample;
the relaxation and C5 calculations are classical method obstructions. They
cannot receive discovery credit, and routine special-class extensions are
excluded. Source/follow-up and current-public novelty gates remain uncleared.

Exact mathematical falsifier: an explicit finite simple graph G, integer
1<=k<=floor(3n/4), and exact certified Laplacian spectra/order-statistic bounds
with mu_k(G)mu_k(complement G)>n(n-k). An out-of-range Proposition19 graph,
an arbitrary PSD spectrum, numerical near-equality or a typo in a reference
does not qualify. The precise remaining gap is the nonlinear order-statistic
bound above for every graph in2<=k<n/2, plus the claimed equality analysis.
No PROOF.md, Lean or manuscript is justified. Credit0, counts untouched.
