# r135: position-coloring gap; Hamming questions publicly resolved

No discovery nomination. No full surviving source proof or counterexample, Lean,
manuscript, or count change. Root alone accepts. Counts inherited:9/39,next40.

## Three precise primary statements

1. Fernández–Klavžar–Kuziak–Muñoz-Márquez–Yero, *On the weak k-metric
dimension of Hamming graphs*, Discrete Optimization60(2026)100945,
Conjecture6.1, actual published PDFp11: for ALL integers n>=3,m>=n+1,
3<=k<=2n, wdim_k(K_n square K_m)=m ceil(k/2) for even k, and
m ceil(k/2)-1 for odd k. Weak resolution requires for EVERY distinct pair
y,z that sum over selected x of |d(y,x)-d(z,x)|>=k. PUBLIC: Kumar,
arXiv2609.32161v1, Theorem2.1/Lemmas2.2–2.3 pp4–5 prove exactly it.
The entire lower bound and cyclic construction proof were read. Its
chronology paragraph reports an August21 GitHub posting and same-day MathDB
proof; those earlier timestamps are author reports here, not independently
authenticated. September26 arXiv posting alone excludes our October29 route.

2. Same primaryp11, following paragraph: wdim_2(K_n square K_m)=m for ALL
n>=3,m>=2n. PUBLIC: Kumar Section2.3, Lemmas2.4–2.9 and Theorem2.10,
proves the stronger exact equality threshold m>=2n-2. Its transversal proof
uses occupied-row degree sums>=4 and all row-pair sums>=2. The current fixed
Omega blueprint HammingWeakTwoMetricDimension further states the exact
remaining below-threshold range4<=n<m<2n-2. Its actual11KB body was read,
not just its filename. No such extension is rebadged. No upstream replay.

3. Chandran S.V.–Di Stefano–Haritha S.–Thomas–Tuite, *Colouring a graph
with position sets*, arXiv2408.13494v2, September10 2025, Definition2.3 and
Conjecture9.3 p26: for EVERY finite simple graph G, n=|V(G)|, and BOTH
pi=gp and pi=mp, chi_pi_i(G)+chi_pi_i(complement G)<=n+1, and the product
is <=((n+1)/2)^2. A color class is independent and contains no three
vertices on one shortest path(gp), respectively one induced path(mp).
Disconnected graphs are explicitly allowed, with componentwise conventions.
The product follows from the sum by AM–GM, not a separate outcome.
Actual currentv2 definitions, Section4 proof bodies and closing conjecture
were read. Retained same-day survey2501.19385v5 pp51–52, Conjecture5.29,
and Section6 list repeat the sum question. The retained survey is supporting
evidence, not a fresh version observation. ORO accepted manuscript returned403;
no retry/bypass. Search-index text agrees on9.3 but does not substitute for
actual primary bytes. No published-journal-body or global novelty PASS.

## Sustained route on the surviving coloring question

Encode edges and all triples contained in a shortest/induced path as forbidden
sets. A legal color is exactly a subset containing none of these forbidden
sets. Every larger violation contains a triple, so this loses no higher-order
path constraint. The exact subset DP recursively selects a legal subset
containing the lowest remaining vertex. For mp it enumerates ALL induced
paths in each sampled graph, rejecting extensions introducing chords. For gp
it uses all-pairs distances and triangle equality with reachable endpoints.

The strongest analytical route investigated is a clique-cover bridge for gp.
Write theta(G)=chi(complement G). Source Theorem4.4 proves chi_gp_i(G)=chi(G)
when diam(G)<=3. If both G and its complement have diameter<=3, classical
Nordhaus–Gaddum applies. If connected G has diameter>=4, its complement has
diameter<=2: otherwise some adjacent u,v in G have no common nonneighbor,
so N_G[u] union N_G[v]=V(G), forcing diameter(G)<=3. Hence the remaining
connected gp branch would follow from

    for every connected G with diam(G)>=4,
    chi_gp_i(G) + theta(G) <= |V(G)|+1.             [UNPROVED]

For disconnected G its complement has diameter<=2. The position chromatic
number is the maximum of component values, while theta is their sum. If the
displayed bridge held for high-diameter components, source4.4/classical NG
give it for other components; selecting a maximizing component and using
theta(H)<=|V(H)| on the rest proves the total bound. This is conditional,
not a proof of the missing bridge.

This diameter argument does NOT transfer to mp: small diameter does not
exclude long induced paths. The unrestricted mp sum inequality is also
unproved; it would imply gp since shortest paths are induced. Even solving
the gp reduction alone would be a partial source result, uncredited here.

## Strongest objection and exact falsifiers

Pair/singleton-only coloring has optimum n-nu(complement G). For K_1,5
this is4, and for its complement5:9>7=n+1. Actual gp/mp values are2
and5: all five leaves form a legal class. Thus matching alone fails; a proof
must exploit larger legal sets with path constraints. This is a route failure,
not a source counterexample. Ordinary proper coloring cannot silently supply
path control either: P5 has chromatic2 but chi_gp_i=chi_mp_i=3, since its
unique bipartition puts three vertices on the same shortest induced path.
Both controls are exactly checked.

Precise gaps: the displayed high-diameter clique-cover bound and a universal
path-sensitive mp coloring argument improving matching when needed. A graph
violating the former blocks that sufficient route only. A certified graph with
chi_pi_i(G)+chi_pi_i(barG)>n+1 refutes the source. Neither was found.
Twenty-five fixed-seed graphs of orders7–11 were exactly solved for both
parameters and complements. This is not an exhaustive census or a theorem
improving the source's up-to-order10 observation. Stronger clique-cover tests
and every sampled adjacency list/optimal partition are in check-results.json.
The216 Hamming constructions only diagnose public mathematics. No finite
check is a proof.

## Historical coverage and registry limits

Before downloads, native exact source-ID/title/author-family queries searched
original SUMMARY/discovery/PROOF/review/DECISION roles. Broad survey query
found r101; its actual complete original discovery concerns lower general
position products/terminal sets, not9.3. Another broad query found r66 via
unrelated language; its actual original discovery concerns Macdonald Turan
ratios. Both actual dispositions were read, not inferred from hit snippets.

The follow-up reuses r133's426515 hash/path aliases, selects1596 original
report paths, adds current changed/new report paths, and queries FULL texts
with exact aliases and no match cutoff. Last screen:1609 paths/1115 distinct
bodies,1596 unchanged,13 changed/new, no missing/oversized selected files,
zero matching bodies. See history-receipt.json for exact aliases, role
exclusions and retained original r111–r113 science. This is REPORT-ROLE
lexical coverage, not all-source semantic absence. Generated extracted,
replay, packet and input roles are excluded; no entire r111–r113 lane is
excluded. No identical400k-file inventory rebuilt.

Retained registry index separately selects2359 FULL tree/path representatives;
20 bodies match broad aliases. All matches retained in registry-retained.json,
no global cutoff. Historical dates and filename roles constrain this coverage;
it is not all registry theorem bodies. Actual Hamming neighbor body opened at
fixed current revision. Regex absence is never novelty clearance.

One live default-HEAD observation23:21UTC: Omega
8a9f34a98b9b36553571808bf4187356a94a25ae; OpenAI
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a unchanged. Fixed
e1ff281c3881e633b86be1072f049a778bdbdc1b to8a9f is ancestor-verified,
12 commits/154 paths, below250/300 API caps. Complete comparison retained;
no moving-HEAD chasing. Diff/path text does not semantically clear all154
files or unmodified bodies. Prior r129/r130/r125/r119 and r3/r4 receipts
remain qualified historical observations, not target semantic clearance.
No current full-tree/all-body novelty PASS is claimed.

## Failures and disposition

Native combined context and one-line JSON grep produced truncated displays;
focused source reads/structured receipts replaced relevant views. Web PDF
fetch timed out; institutional primary PDF then succeeded. Guessed successor
v2 URL returned404; actual abs history identifiesv1 and its latest PDF was
obtained. No404 is inferred to mean no resolution. Successor extraction has
a font warning; theorem/proof text is readable. Journal403 respected.
An initial discovery.md apply_patch was rejected for a missing line prefix;
no partial file was written, and corrected patch succeeded.

No cap raise, unguarded Python, browser, git, external message or shared edit.
No PROOF.md: public Hamming mathematics is excluded, and the surviving
coloring question remains unresolved. No investment clearance requested.
