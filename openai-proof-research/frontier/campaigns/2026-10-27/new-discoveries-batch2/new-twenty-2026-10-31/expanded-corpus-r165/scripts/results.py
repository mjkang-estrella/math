import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'extracted.json').read_text())
R={}
def put(i,outcome,depth,disp,attempts,remaining,extra=None):
    e=ex[str(i)]
    R[str(i)]=dict(mathdb_id=i,title=e['title'],literal_statement=e['statement'],source_url=e['source_url'],provenance=e['provenance'],
      raw_line_file=f'raw/{i}.jsonl',outcome=outcome,review_depth=depth,disposition=disp,mathematical_attempts_and_coverage=attempts,
      precise_remaining_gap=remaining,lean_endpoint=None,lean_run_in_lane=False,accepted_credit=0,proposed_credit=0,self_accepted=False,
      novelty_cleared=False,**(extra or {}))
put(334808,'EXCLUDED_KNOWN_RESOLUTION',
 'Primary source arXiv:1612.02843v1 read: Sections 1.3 and 2 (MMD/boundary definitions, Remark 2, Lemmas 8-9, Theorem 10, Proposition 16, Conjecture 17). Prior art: arXiv:2008.04282 body read (Section on realization, p. with refs [5]); the cited note itself not fetched.',
 'Conjecture 17 (G_SR on the boundary is never K_{r,s}, r,s>=2) is TRUE and already settled: R. Lenin, "A short note on: There is no graph G with G_SR = K_{r,s}", Discrete Appl. Math. 265 (2019) 204-205, cited as the settlement in arXiv:2008.04282 ("Their conjecture was settled in [5]"). This lane independently found a one-paragraph proof (NOTES.md section 1): maximal geodesic extension of v1 v v2 gives an MMD pair x,y with v not MMD to either, contradicting complete bipartiteness unless every boundary vertex is simplicial, whence G_SR is complete (source Theorem 10). The proof uses only the source Lemma 8/9 idea plus a standard strengthening, so it would be zero credit even without the 2019 note.',
 'Exact MMD/boundary computation (scripts/srg_lib.py, srg_search.py; self-test reproduces source Figure 5, C5, C6, trees, K33). Exhaustive over all connected graphs of orders 4-9 (6+21+112+853+11117+261080 graphs, McKay lists) and the first 3,000,000 of the 11,716,571 connected order-10 graphs (chunks 0-2,999,999 of graph10c.g6.gz): 0 realizations; search stopped after the prior-art finding. Logs logs/srg-*.',
 'None (settled).',{'prior_resolution':'Lenin, DAM 265 (2019) 204-205, via arXiv:2008.04282 ref [5] (sources/prior-2008.04282.pdf sha256 470fe6cf...)'})
put(334872,'PARKED_HARD_GAP','Abstract/current version (v1 only) read; MathDB literal statement.',
 'RNC completeness for MDS extensions of Reed-Solomon codes: implied by the MDS conjecture; Ball (q prime) and Ball-De Beule (k <= 2p-2) settle large families, but the general q = p^h case is open. No finite certificate can refute it (verified small-q classifications agree), and a proof is an MDS-conjecture-level problem.',
 'No computation (search space would be arc classification in PG(m-1,q); known tables already consistent).','Full MDS-type extension classification for non-prime q and large m.')
put(334925,'PARKED_AFTER_ANALYSIS','Primary source arXiv:1612.07652v3 Sections 1-2 read (Conjecture 2.2, Theorems 1.6, 2.1, 2.3, 2.7, Example 2.6); v1 also fetched.',
 'Almost 1/zeta-fair representation in dimatroids. Source proves partitions into two sets (Theorem 2.7, slightly weaker) and the two-partition-matroids-with-parts-of-size-2 case. For bipartite matching complexes (zeta = max degree Delta) a counterexample needs at least two parts of size >= 2 Delta with requirement >= 1; for two parts an edge meets at most 2 Delta - 1 edges, so two-part violations are impossible; total requirement sum |A_i|/Delta - m is below nu >= |E|/Delta by m, so small counterexamples are implausible. Not settled.',
 'Analytic slack argument only; no exhaustive matroid enumeration (no matroid database in lane; pure-python enumeration of matroid pairs beyond 7 elements infeasible under caps).','General dimatroid exchange lemma (source Conjecture 4.2) or an explicit multi-part obstruction.')
put(339813,'PARKED_HARD_GAP','Primary source arXiv:1807.04741v1 Sections 2 and 6 read (Conjectures 2.4, 6.4, 6.5); sibling records 339810/339812 parked by fresh-corpus-r20.',
 'Kotesovec period lcm[F_q] (F_0=F_1=1). Periods themselves are known only empirically (Kotesovec data through q=7 agrees). A refutation needs the exact period of the q=8 queens quasipolynomial; a proof needs the denominator conjecture 6.5 plus period = denominator (Conjecture 2.4). No finite certificate within reach; Lean formalization of inside-out Ehrhart quasipolynomial periods is far beyond campaign cost.',
 'None beyond source reading (r20 already tried exact vertex systems for the sibling denominator conjecture).','Exact period computation for q=8 or a structural Fibonacci-denominator theorem.')
put(329577,'PARKED_NUMERICALLY_SUPPORTED','Primary source arXiv:1501.00573v1 read (Conjecture 5.3 and the remark a_r=(2r+1)!!^2; Sections 1-2 method). Web search found no later proof (Mao arXiv:1511.06221 settles Conjecture 5.2, not 5.3).',
 'Guo-Liu Conjecture 5.3. Exact rational computation (scripts/r329577.py) of the least a_r(N) = lcm_{n<=N} denominator(S_n/n) for r=0..7, N=120: a_r stabilises at 1, 9, 225, 3675, 99225, 2401245, 135270135, 289864575 from n<=10 onward, each dividing (2r+1)!!^2. Conjecture strongly supported. Christoffel-Darboux for shifted Legendre polynomials gives S_n = n (L_r x L_r)(Q_n)/2 with Q_n integral (NOTES.md section 4), which explains the factor n but not the bounded denominator. A uniform proof would most likely follow the source multivariable-Zeilberger plus binomial-divisibility route: high risk of the same routine-source-adaptation exclusion as the root Guo divisibility ruling (lanes/root-guo-divisibility-review-adoption-r1/DECISION.md), and Lean-heavy.',
 'r=0..7, n<=120 exact (logs/r329577.log).','A uniform-in-r denominator bound for (L_r x L_r)(Q_n)/2, i.e. (2r+1)!!^2-integrality for all n.')
put(329610,'PARKED_LITERAL_ONLY','Abstract and current version (v2, 2018) read; body not read.',
 'Attainment of a Mahler-volume lower bound defined through a source-specific variational constant alpha(n); analytic convex geometry, outside the finite-certificate scope; the literal statement depends on the unrecovered definition of alpha(n).',
 'None.','Recover alpha(n) and decide whether the localisation bound is sharp.')
put(329760,'PARKED_HARD_GAP','Abstract read; MathDB statement; literature status via web search (source verified n<=25 by randomised guess-and-check and k<=6 by proof; Hicks-Ollis-Schmitt arXiv:1809.02684 polynomial method). Sibling 329765/329766 parked by fresh-corpus-r9.',
 'Archdeacon-Dinitz-Mattern-Stinson partial-sum sequencing (contains Alspach-type sequencing). Large partial-resolution literature (family warning); counterexample search beyond n=25 needs all subsets of Z_n with an ordering search per subset (2^25 subsets), infeasible under lane caps; no exact mechanism for a full proof.',
 'None (deliberately not repeated).','Uniform proof for all k in all cyclic groups.')
put(330216,'EXCLUDED_KNOWN_RESOLUTION','Abstract of the source itself read (v3, Combinatorica 37(6) 2017).',
 'The MathDB record says the source supplies no resolution, but the source IS the resolution: Muetze and Su, "Bipartite Kneser graphs are Hamiltonian", Combinatorica 37 (2017) 1207-1219, prove H(n,k) Hamiltonian for all k>=1, n>=2k+1. MathDB paraphrase defect; zero credit.',
 'None needed.','None.')
put(330252,'EXCLUDED_KNOWN_RESOLUTION','Source abstract (v1) read; prior resolution body read by expanded-corpus-r71 (record 376135: arXiv:2607.17983 Theorem 1.6 and its proof via Theorems 1.4/1.5).',
 'fvs(G) <= m/g for planar graphs of girth g is the Dross-Montassier-Pinlou conjecture, confirmed in arXiv:2607.17983 (2026) via a planar signed-graph frustration bound; see expanded-corpus-r71/results.json 376135. Zero credit.',
 'None.','None.')
put(330285,'PARKED_SOURCE_DEFINITION_DEFECT','Primary source arXiv:1504.03662v2 Sections 1 and 3 read (Definitions 1.1-1.4, 3.1-3.2, Conjectures 3.1-3.3).',
 'The source defines "critical for dimension d" by EDGE removal (Definition 3.1) while Conjecture 3.2 and MathDB speak of vertex deletion; the faithful orthogonal rank rho_perp (real-algebraic) has no exact computable characterisation in the source, and its sample values (e.g. "Petersen banned to dim 2, rho_perp(P)=3") are unsupported. No well-posed finite target; note that any graph with a nontrivial automorphism trivially has two isomorphic vertices, so a counterexample must be vertex-deck-distinct and critical, which cannot be certified without an exact rho_perp oracle.',
 'None.','A precise definition and an exact algorithm for rho_perp.')
put(330593,'PARKED_HARD_GAP','Abstract (v3) read; siblings 330598 (expanded-corpus-r80) and Ruckle items (expanded-corpus-r142) already parked.',
 'Refined Kikuta-Ruckle conjecture: continuous optimisation over probability vectors with source-displayed finite set for s; the literal record omits the set ("exactly as in the source"); the known Kikuta-Ruckle cases do not cover it. No finite certificate.',
 'None (siblings not repeated).','Optimality of equal-weight solutions for all (n,k,d).')
put(330655,'PARKED_LITERAL_WORDING_DEFECT','Abstract (v2, DCG 2016) read.',
 'Exoo conjectured chi(G_[a,b])=7 only for SUFFICIENTLY SMALL positive b-a. The MathDB "for any epsilon>0" is trivially false: for epsilon>=1 every two points at distance <=2 are adjacent, so a unit disc is an uncountable clique and chi is infinite. That literal refutation is a zero-credit wording correction; the intended small-epsilon conjecture is open (source proves chi>=5).',
 'None.','Intended statement: chi(G_eps)=7 for all small eps (needs >=7 lower bound; open).')
put(330666,'PARKED_HARD_GAP','Abstract (v2, accepted EJC) read.',
 'Nonexistence of linear perfect l2 codes for n>3, r>1: infinite family in dimension and radius; source settles n=2,3 and gives packing bounds. No finite counterexample mechanism (existence would need a lattice tiling by a discrete l2 ball in dimension >=4, contradicting known polyomino-tiling evidence); proof needs new geometry.',
 'None.','Nonexistence in all dimensions n>=4.')
put(330713,'EXCLUDED_KNOWN_RESOLUTION','Primary source arXiv:1506.04640v2 introduction read (Theorem 3, Conjecture (Lee-Zhang), Labourie remark).',
 'Source proves the n=3 case (Theorem 3) and records Labourie\'s explanation that the Lee-Zhang conjecture fails for n>=4 (Hitchin representations into PSp(2k,R), PSO(k,k+1)); the general statement is thus already refuted in the source and a modified conjecture is proposed. Zero credit.',
 'None.','None.')
put(331313,'EXCLUDED_KNOWN_RESOLUTION','Primary source arXiv:1509.01185v1 Section 4 read (Conjecture 12, Theorem 13 Wu). Prior resolution: arXiv:2202.08123 abstract read (Wang and Wu, JCTB 2024 per web search).',
 'Conjecture 12 is proved in full by Yan Wang and Hehui Wu, "Graph partitions under average degree constraint" (arXiv:2202.08123): every graph of average degree >= s+t+2 has a vertex bipartition with parts of average degree >= s and >= t, i.e. exactly e(G)>=(s+t+1)v(G) => e(G[A])>=s|A|, e(G[B])>=t|B| after halving s,t. Zero credit.',
 'Exact staircase checker (scripts/dense_part.py, exact rationals, all 2^n-2 bipartitions; worst (s,t) at Pareto corners) on all connected graphs of orders 4-9 (273,189 graphs): 0 violations; minimum slack 0 attained only by K_n (corner-tight), next 1/n by K_n minus an edge. Logs logs/dense-*.',
 'None (settled).',{'prior_resolution':'Wang-Wu arXiv:2202.08123 (sources/prior-2202.08123-abs.html sha256 5e85ea7f...)'})
put(331481,'PARKED_LITERAL_ONLY','Abstract (v4, Discrete Analysis) read.',
 'Dimension-free constant in uniform-cover stability: analytic/information-theoretic, asymptotic in d; outside finite-certificate scope.',
 'None.','Dimension-free entropy stability argument.')
put(331535,'EXCLUDED_ROUTINE_COROLLARY_OF_PUBLIC_THEOREM','Source abstract and author error note (v2) read; sibling 331534 parked by expanded-corpus-r138. Public prior: openai/cdc-lean README and Main.lean endpoint read (not rebuilt).',
 'For k=3 the statement is the cycle double cover conjecture for cubic bridgeless graphs. The CDC theorem is now public with a kernel-checked Lean endpoint: openai/cdc-lean (created 2026-06-24, last push 2026-07-09), theorem CDCLean.cycleDoubleCover_of_bridgeless : Nonempty G.CycleDoubleCover for every finite loopless bridgeless multigraph (via Jaeger-Kilpatrick eight-flow and cubic expansion); also indexed in Lean Pool candidates (jarfo/cdc-statements etc.). The full regular statement then follows routinely (NOTES.md section 3): k odd: (k-1)/2 copies of a CDC; k even: the k-regular graph is Eulerian, so a circuit decomposition plus (k-2)/2 copies of a CDC (k-1>=1 gives bridgeless for k>=2; k<=2 trivial). Zero credit.',
 'Reduction proof only.','None (subject to the public CDC proof; its body was not audited here).')
put(331543,'PARKED_HARD_GAP_CREDITED_FAMILY','Abstract (v2) read; status via web search (Goddyn-Halasz: abelian Cayley tables have chi = n or n+2, and chi(L) = n + o(n); cyclic case simplified arXiv:2109.01194).',
 'Latin-square chromatic bound implies Brualdi-Stein and Ryser-type transversal conjectures; source verified n<=8 for all main classes. Exhaustive extension to n=9 (about 1.93e10 main classes) with exact chromatic number is far beyond Python caps; Latin squares are an already-credited family (381433, 347712). Park.',
 'None.','Full conjecture (transversal-strength).')
put(331819,'EXCLUDED_CLASSICAL_COUNTEREXAMPLE','Primary source arXiv:1511.05384v1 read (abstract definitions; Section 4 Conjecture 4.4, Remark 4.5, Theorem 4.6).',
 'MathDB paraphrase defect: psi_k is the minimum k-path vertex cover number, not a path count (under the paraphrase a 5-vertex spider with legs 1,1,2 already refutes it, also zero credit). With the source definition, for n>=3: psi_{n-1}(G)=2 iff every vertex-deleted subgraph G-v is traceable (no single vertex meets all (n-1)-paths iff each G-v has a Hamilton path, and any two vertices always meet every (n-1)-path), and psi_n(G)=1 iff G is traceable. So Conjecture 4.4 is equivalent to the nonexistence of hypotraceable graphs, which exist classically (Horton 40-vertex example reported by Gruenbaum 1974; Thomassen, Discrete Math. 9 (1974) 91-96, 34 vertices). Refuted by a classical construction: zero credit (372630 precedent); also a 34+-vertex non-traceability certificate is Lean-expensive.',
 'Equivalence proof (NOTES.md section 2); no computation needed.','None.')
put(331893,'PARKED_HARD_GAP','Abstract (v2 2021, Adv. Appl. Math. 2018) read.',
 'Warmth <= ind(Hom(K2,G))+2: warmth is defined by asymptotics of d-branching walks and the Z2-index is topological; neither is finitely computable in general, so no finite certificate is available. Park.',
 'None.','Topological lower bound linking warmth to Z2-index.')
assert len(R)==20 and set(R)==set(str(i) for i in json.loads((L/'reservation.json').read_text())['ids'])
(L/'results.json').write_text(json.dumps(R,indent=1,ensure_ascii=False)+'\n'); print('wrote',len(R))
