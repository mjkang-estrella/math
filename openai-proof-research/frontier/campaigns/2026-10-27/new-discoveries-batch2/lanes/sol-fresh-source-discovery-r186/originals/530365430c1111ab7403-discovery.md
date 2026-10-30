# r102: clique–path saturation — unresolved, credit 0

Counts remain **8 additional / 38 total**. No full ordinary result, no PROOF.md, no Lean or paper. All work is local to this lane. Two fresh attributed questions below belong to one source family; they are not two discovery nominations.

## Actual source and two fresh questions

Huaqin Li, Lihua You, Xiaoxue Zhang, *Saturation numbers of K_3 vee P_k*, arXiv:2610.34990v1, submitted 26 October 2026. Latest live abstract history lists v1 only. Actual HTML body, Conjecture 1.1, Theorem 1.2, Section 2, proof Section 3 and final Section 4 read. Source bytes are saved as sources/sat.html, with literal extracted text and abs history. This is the recent primary successor to X. Zhang, L. You, X. Zhao, *Saturation numbers of K_2 vee P_k*, Discrete Applied Mathematics 394 (2026), 62–80, DOI 10.1016/j.dam.2026.07.005.

**Question A: full Conjecture 1.1, attributed to Zhang–You–Zhao.** For all integers k,s>=3 and n>=a_k+s,

sat(n,K_s vee P_k) = binom(s,2)+s(n-s)+sat(n-s,P_k),

where a_k=k for 3<=k<=5; a_(2t)=3*2^(t-1)-2 for 2t>=6; a_(2t+1)=2^(t+1)-2 for 2t+1>=7. P_k has k vertices. Graphs are finite simple undirected graphs. A forbidden copy is a subgraph, with extra host edges allowed. H-saturated means H-free and adding **every** missing edge creates H, on the original vertex set. The minimum ranges over all n-vertex hosts, without a connectivity restriction.

**Question B: Li–You–Zhang Section 4's explicit classification problem.** Characterize all minimum (K_3 vee P_k)-saturated graphs. The investigated domain is the paper's k>=3, n>=a_k+3. “Minimum” means attaining the saturation number, not just inclusion-maximal H-freeness. This is a real source question, but its complete classification is not supplied here. The source itself settles the number for s=3, not this classification.

The successor Theorem 1.2 proves the full s=3 numerical case, and Section 2 quotes the s=2 case and ordinary path saturation formulas. These are prior results, never credited. Proposition 2.3 already supplies the upper bound for every s. The residual numerical question is the uniform lower bound for unbounded s>=4. A fixed s, fixed k, or classification example is not a qualifying outcome.

Original publisher access: Crossref returned the exact title/DOI, but the DOI response is only an Elsevier redirect document; its ordinary publisher destination returned 403. No retry/bypass. The original journal conjecture/proof body is **not** independently read. Attribution rests on the actual current primary successor's printed statement and bibliography, not on metadata pretending to be that original body.

## Early duplicate and live public screen

Before mathematical investment, read ancestor/batch AGENTS, NEXT, ledger, prior-campaign-context and the final-freeze complete registry baseline; context identities saved. The all-date lexical corpus hashes 5984 SUMMARY/discovery/FINDINGS/PROOF/review/ledger-name files across openai-proof-research, including old campaigns and frozen copies. The first screen correctly rejected Pereyra's W2 threshold (r68/r85, publicly proved), Omar's general domination-unimodality lead (r70/r78), Xie–Xu's dependence/2-matroid family (r30), and Leake–Mohammadi Yekta's global fiber-count Q1.7 (r52/r77/r80). Those bodies were fetched to read scope, then dropped; none received computations or a proof attack. AutoGraphForge's two printed annihilation/edge-cover inequalities already have classical proofs in that source; no unprinted survivor was promoted. A guessed dependence-paper URL 2412.20332 was unrelated and discarded; the correct 2408.09152 body was obtained only for duplicate identification. The selected questions A/B had no exact prior local match in the bounded screen. Broad fort/author-name hits were unrelated; no forts question was selected.

Fresh registry default heads: Omega c9cea079996532f43216352b68960a727b7ed8fe; OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Omega compare from r101's 556e7696bbabaff203d45456d177c5ce5b714212 reports 19 commits / 8 files; actual pinned bodies of all eight obtained. The complete 18:13 baseline and supplied r99/r101 dated chain are inherited, not semantic clearance. Targeted baseline path search found the nearby MatchingConeLeafExistence/Universality and WangTianStrongSaturationRefutation Blueprints, whose actual current bodies were read separately. Their forbidden graphs/scopes differ: an eight-vertex matching cone, or strong directed connectivity. The actual matching-cone Lean body and OpenAI CycleClique/Construction/PathJoining Lean body were obtained and compared; the latter joins paths to a cycle, with no saturation theorem. Blueprint and Lean are kept distinct. No external Lean replay or audit of upstream truth was done. This bounded inventory/body comparison is not worldwide priority clearance.

Bounded exact-title public searches found the October26 successor, source s2 article and classical survey; no full all-s successor was located. This is not evidence that no such proof exists. Current-registry target terms and chronology limits, publisher 403 and original-body gap remain explicit.

Closest accessible classical body: Faudree–Faudree–Schmitt, *A survey of minimum saturated graphs*, actual PDF Section4.2/Theorem19 and its preceding structure discussion. It attributes path saturation to Kászonyi–Tuza1986, describes almost binary tree components, and gives the large-n formula. That full original1986 proof is not independently obtained. Source Theorem2.1 gives the small k formulas separately. Nothing here claims a new path saturation theorem, new join upper bound or novel universal-vertex lemma.

## Sustained full-scope attack: deletion plus exact charging

Write H_(s,k)=K_s vee P_k and q=sat(n-s,P_k). Let T=s*n-s(s+1)/2+q. The already-public upper bound is T. The attack seeks e(G)>=T for **every** H_(s,k)-saturated G, for all source parameters.

First, a universal vertex u permits deletion: G-u is H_(s-1,k)-saturated. Here is the exact equivalence, without silently requiring that new copies map u to the designated center. In a cone G=K1 vee F and a forbidden cone H=K1 vee J, an H-copy can be rearranged to use the host universal vertex as its cone vertex. If u is outside the copy, replace the designated cone vertex by u. If u occupies a J-role, interchange u with the designated cone vertex: the old designated cone vertex is adjacent to every other copied vertex, hence fills the old J-role. Therefore G contains H iff F contains J. Apply this also after any missing edge of F. It gives saturation in both directions. Counting edges yields e(G)=n-1+e(F). Assuming the conjecture for s-1, its desired bound becomes exactly T. This is source Proposition2.4's routine mechanism, not a discovery.

For a noncomplete saturated G choose a minimum-degree vertex v, let A=N(v), d=|A|, B=V\(A union {v}), and r=d-s. Source Proposition2.5 ensures d>=s and, for every b in B, the common neighborhood A intersect N(b) contains a clique of order s: a new H-copy uses vb, and its roles put vb into a K_(s+2) copy after addition. Removing vb leaves the required old s-clique of common neighbors. In particular |A intersect N(b)|>=s.

Define the actual nonnegative excess

X=sum_(b in B)(|N(b) intersect A|-s),
C=e(G[A])-binom(s,2)+X+e(G[B]).

The binomial subtraction is justified when B is nonempty, because A contains an s-clique. Partitioning edges gives the **exact** identity

e(G)=s*n-s(s+1)/2-(s-1)r+C.                     (1)

Indeed the four contributions are d, e(A), s(n-d-1)+X and e(B). Thus the entire missing lower bound, in the hard class, is precisely

C >= (s-1)r + sat(n-s,P_k).                    (2)

This is a precise gap, not an assumed theorem or a proof by naming the original conjecture. It specifies the required unpaid edge charges, their host partition, and the deficit that a proposed discharging rule must cover. The source s3 proof performs detailed local-neighborhood cases; its degree bounds and clique types do not supply (2) uniformly as s grows.

Two parts of the degree range need no new estimate. If d=s then A has size s and each b is adjacent to all of A; A is a clique and is universal in G. Deletion applies (or G=K_s vee F with F path-saturated). If d>=2s+2, the degree sum gives e(G)>=n(s+1), whereas q<=n-s by the source formulas, and therefore T< n(s+1). Complete hosts cannot be H-free here because n>=s+k. Consequently a new proof need only address the full, still-unbounded window

s+1 <= delta(G) <= 2s+1,

with no universal vertex. It must use the actual path role in the saturation witnesses, rather than only their s-cliques. No rule proving (2) in that window was found.

An exact alternative formulation makes this role requirement explicit. G contains H_(s,k) iff some s-clique C0 has a k-vertex path in G[intersection_(c in C0)N(c)]. Necessity and sufficiency are immediate by splitting the forbidden copy into its center and path. In G+xy the new edge may be a center edge, a center–path edge, or a path edge; fixing it to the third role would omit legitimate saturation witnesses. A covering/assignment of missing edges to these three witness types still needs a global charging argument; no bounded-multiplicity assignment is proved.

## Strong objections and exact route falsifiers

1. **Local clique witnesses alone cannot pay the path term.** For every s>=2,k>=3 take K_s vee independent_(n-s), n>=s+k. Every missing pair has the required common K_s, diameter2, and delta=s, but e=s*n-s(s+1)/2<T. It is H-free and remains H-free after adding any one missing edge. To see the latter, neither added-edge endpoint can be a center: its new degree is s+1, below the required s+k-1. Thus all s centers would have to be the old K_s and the remaining graph has just one edge, with no P_k. This is a counterexample to the relaxed local-data route, **not** a source counterexample because it is not saturated.

2. **Universal deletion is not available for every saturated host.** For s>=2,k>=3, set t=ceil(k/2) and take the complete (s+1)-partite graph with t vertices in every part. It is H-free by chromatic number: H has chromatic number s+2. Add xy within one part; choose x,y as two center vertices and one vertex in each of s-2 other parts as the remaining centers. The two unused parts support an alternating P_k, since each has t vertices. This constructs the forbidden copy for every missing edge. The host is saturated and has no universal vertex. Its edge count is not an extremal counterexample. Any deletion-based full proof must first establish an extremal structural assertion, or pay (2) directly.

3. **The simplest full classification guess is false even at the source boundary.** At s=k=3,n=6, let G=K6 minus two disjoint edges. It has13 edges, is H_(3,3)-free because H_(3,3)=K6 minus one edge, and adding either missing edge creates H. Every H-free graph on6 vertices has at most13 edges, and every saturated such graph must have exactly13: if it had <=12, adding one edge still leaves <=13, too few for H. Hence this G is minimum. It has exactly two universal vertices, not three. It is not K3 vee a minimum P3-saturated graph. This defeats that classification shortcut, not the numerical conjecture. No credit is sought for this routine endpoint observation.

Strongest genuine falsifier of Question A would be one source-domain saturated graph with fewer than T edges, with H-freeness and all missing-edge copies certified. None is found. For Question B no complete structural characterization is established; the example above only rules out one proposed form. No claim of resolving either source question is made.

## Verification, failures, disposition

check.py is network-free and runs under the unchanged supplied improved helper_guard.py: AS/groupRSS512MiB, CPU210s, wall230s, nominal40ms, BLAS1. It validates 20 local-data obstruction instances, nine genuinely saturated nonuniversal multipartite hosts, 1096 exhaustive cone-deletion identities, the exact charge identity/common-clique conditions in those nine hosts, and all32768 labeled six-vertex graphs for H_(3,3), giving minimum13 with105 labeled minima. These checks test the stated identities and obstructions; they neither prove (2) nor establish general classification. 1174 explicit assertions at least; guard exit0, no resource kill. run.sh is the capped exact replay entry point.

The initial text reader failed once because bs4 was unavailable; replaced with standard-library HTMLParser, no dependency install. A sed replacement expanded an ampersand while constructing the classical retrieval script and caused a syntax error; fixed before retrieval. Both failures are preserved honestly. One tiny Python file-edit helper (replacing the missing bs4 parser) was inadvertently run without the mandatory guard; it performed no search, retrieval or heavy computation. This is a procedural deviation, not silently declared compliant. All research/retrieval/check helpers otherwise ran under the unchanged guard; no caps were raised. The earlier ordered-set-partition OOM recovery instructions were read, and no materialization/retry of that failed workload occurred.

Disposition: UNRESOLVED. Substantive full-scope estimate (2), complete extremizer classification, original s2 journal body and original classical proof-body gaps remain. No full ordinary result to review, no PROOF.md, no Lean/paper investment, no quota claim. Reserved Matveeva/Chatterjee, parked MMPP, r101 and all exhausted/credited families were left untouched.
