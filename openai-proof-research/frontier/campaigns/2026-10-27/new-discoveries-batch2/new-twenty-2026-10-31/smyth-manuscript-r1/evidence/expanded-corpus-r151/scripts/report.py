import json, pathlib, glob
D=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((D/'extracted.json').read_text()); res=json.loads((D/'reservation.json').read_text())
rows={r['mathdb_id']:r for r in res['rows']}
abs_info=json.loads((D/'outputs/arxiv-abs-info.json').read_text())
def receipts(arx):
    out=[]
    for a in arx:
        for kind,p in (('abs',D/f'sources/abs-{a}.receipt.json'),('pdf',D/f'sources/pdf/{a}.receipt.json')):
            if p.exists():
                r=json.loads(p.read_text()); out.append({'kind':kind,'url':r['url'],'utc':r['utc'],'status':r.get('status'),'sha256':r.get('sha256'),'bytes':r.get('bytes')})
    return out
H='history: campaign *.md/*.json grep for the ID (outputs/history-id-matches.txt) found only index/queue/ledger launch entries; arXiv-ID/title grep (outputs/history-arxiv-matches.txt) found no prior disposition'
E={}
def add(i,arx,outcome,depth,mech,remaining,coverage=None,extra_hist=None):
    E[i]=dict(arx=arx,outcome=outcome,depth=depth,mech=mech,remaining=remaining,coverage=coverage,hist=(H+('; '+extra_hist if extra_hist else '')))
add(332446,['1602.03338'],'SETTLED_PUBLISHED_RESOLUTION','source body read (Sec. 1.3, conjecture); prior-art abstract read (Hakopian-Vardanyan, Adv. Comput. Math. 2019, arXiv:1807.08182) via web search, body not fetched',
 'Hakopian and Vardanyan, "On the usage of lines in GC_n sets" (Adv. Comput. Math. 2019, arXiv:1807.08182) prove, under the Gasca-Maeztu hypothesis, the corrected statement: a k-node line is either unused or used by exactly C(s,2) nodes with 2k-n-1 <= s <= k. The literal printed conjecture (no "unused" alternative) is therefore already corrected/settled in print; any residual literal counterexample is a published correction. Zero credit.',
 'none for credit')
add(332504,['1602.04881'],'PARKED_DEEP_MODEL_DEPENDENT','source body read (Sec. 5, Conjecture 23, results preceding it)',
 'Conjecture 23 asserts that the two sufficient conditions proved in the source (unboundedly long sub-paths of quotient graphs, or unboundedly long shortest cycles) are also necessary for universality. The necessity direction requires an impossibility theorem for whole classes of oblivious-robot systems; no finite certificate or small-instance search applies. Lean cost: a full model of the robot computation semantics. Not pursued.',
 'a necessity (impossibility) proof for classes with bounded quotient sub-paths and bounded girth')
add(332627,['1603.01189'],'SETTLED_PUBLISHED_RESOLUTION','source statement read; prior art identified by web search: Pagaria (IMRN 2023, complete graphs) and Crowley-Proudfoot arXiv:2505.05324 (May 2025, general graphs); bodies not fetched',
 'The complete-graph case (Moseley-Proudfoot-Young conjecture) was proved by Pagaria (IMRN 2023); the graph-generalized version was proved by Crowley and Proudfoot (arXiv:2505.05324, 2025), who state it was previously known only for complete graphs. Public resolution; zero credit.',
 'none for credit (record: Crowley-Proudfoot body not read in this lane)')
add(335792,['1704.02921','1809.03268'],'PARKED_AFTER_EXHAUSTIVE_SEARCH','source body read in full (Thm 1, Conj 1, Prop 1); Frick, Israel J. Math. 2020 (arXiv:1809.03268) Sec. 6 read: q=3 still undecided there',
 'Exact checker (scripts/fairsplit.py; per-colouring memoised DFS over labels {S_1..S_q, removed}) of the literal Conjecture 1 (classes of size >= q-1; exactly q-1 removed per class; q-stable sets; sizes differing by <= 1; lower bound floor((|V_j|+1)/q)-1). Validated against the proved case q=2 for N <= 11. No counterexample anywhere searched. A proof for prime q appears to need Z_q-Tucker/stable-Kneser-hypergraph machinery that Frick (2020) could not complete; not attempted further.',
 'a proof for q=3 (smallest open case); counterexample search beyond the coverage below',
 coverage={'q=3, all colourings up to reversal':'N <= 13 (N=13: 1,818,670 colourings, two chunks)','q=3, at most 2 classes':'N <= 21','q=3, at most 3 classes':'N <= 14','q=5':'N <= 15 (N=15: 499,417 colourings)','q=6':'N <= 16','q=2 validation':'N <= 11','logs':'logs/fair-*.log'})
add(336137,['1705.08150'],'PARKED_PRE_2012_ORIGIN_AFTER_SMALL_SEARCH','source Sec. 1-2 read (Conjecture 1 with references [6],[20])',
 'The (1,1)-matrix conjecture is attributed in the source to Bartnicki-Grytczuk-Niwczyk (J. Graph Theory 2009) / Wong-Zhu (J. Graph Theory 2011), so it predates the 2012 rule despite the MathDB year 2017, and it is a well-studied strengthening in the 1-2-3 / (2,2)-choosability circle. Small check (scripts/perm11.py): for every graph on <= 6 vertices (156 isomorphism classes) a column choice with nonzero permanent was found by random Ryser sampling (no exact fallback needed). No counterexample expected at small order; no proof route.',
 'general proof; no finite route',
 coverage={'all graphs':'n <= 6 (156 graphs)','log':'logs/perm11.log'})
add(336854,['1708.05075'],'PARKED_INFINITE_STRUCTURAL_WITH_SUPPORTING_SEARCH','source body read (definitions Sec. 2-3, Theorems 4-6, Conclusion, Conjecture 1)',
 'Open part: k=2 with c <= 9 and all k >= 3 (k=1 is Theorem 4; k=2, c >= 10 follows from Theorems 5-6). Heuristic structure: linear co-size forces a long ordered line with bounded gadgets at its ends; for a far point x, a pair {g,h} is aligned iff (x g h) or (x h g). By (P4), a triple whose three pairs are all aligned is collinear, so every local triangle contains a non-aligned pair and the non-aligned pairs (exactly k of them) cover H(B). This supports the conjecture but needs a general structure theorem (bounded gadgets, consistency of alignment for all far points). Random search (scripts/betweenness.py) of path-plus-gadget weighted-graph metrics: about 2,240 instances whose co-size was exactly linear (slopes k=1..6) over n in a window; none had a triangle cover number > k. No counterexample; an infinite statement with no finite certificate.',
 'structure theorem: almost-metrizable structures of co-size kn-c and large n are a line plus O_k(1) end gadgets with consistent alignment',
 coverage={'random metric gadgets':'~2,240 exactly-linear instances (1,509 + 52 one-end, 679 two-end), slopes 1..6, gadgets of 2-4 vertices at one or both path ends, L in {13,14,15} or {14,15,16}','logs':'logs/btw-*.log'})
add(338235,['1801.06034'],'PARKED_EVENTUAL_STATEMENT','source body read (Sec. 4: Theorem 4.1, Conjectures 4.2-4.4; v4 comment "corrected Conjecture 6.1" checked: the correction concerns Conjecture 6.1 on H_q(l,k), not this Conjecture 4.4)',
 'MathDB 338235 is Conjecture 4.4 (existence of n_q). The source proves q in {2,3,4,5} (Theorem 4.1), and the asymptotic statement is equivalent to the eventual non-existence of non-trivial Cameron-Liebler-type classes, an infinite problem with no finite certificate. Not pursued.',
 'eventual triviality for q >= 7 (Cameron-Liebler line classes in PG(n-1,q) for large n)')
add(339497,['1806.04188','2011.06625'],'PARKED_BOUNDED_CHI_INFINITE','source abstract and conjecture section read; Nelson arXiv:2011.06625 abstract (I_{1,t}-free case) via web search',
 'Bounded critical number for simple binary matroids with no induced I_s and no triangle: open. The source notes s in {1,2,3} is easy; Nelson proves the I_{1,t}-free case. An infinite chi-boundedness statement with no finite certificate.',
 'general s')
add(341257,['1812.01517'],'PARKED_INFINITE_FAMILY_OF_MOVES','source Sec. 5.2 (Conjectures 3-4) and Appendix A read; sibling 341256 excluded in r131 (routine bridge)',
 'Conjecture 4 asks for a conditional local move for every n >= 3 on the polygonal networks Pi_n, with an n mod 4 pattern. The source only has conjectural formulas for small n, verified numerically. A resolution needs explicit grove-type formulas for all n plus response-matrix identities, an infinite symbolic problem; no finite certificate. Not pursued (r131 already disposed of the hexagon sibling 341256).',
 'explicit move and formulas for general n')
add(341638,['1901.07509','2202.12229'],'EXCLUDED_VACUOUS_AS_PRINTED_AND_INTENDED_VERSION_SOURCE_CONTRADICTED','source Sec. V read in full (Lemmas 2-4, definition of good relation, Conjectures 1-2); 2022 follow-up arXiv:2202.12229 introduction and Remarks 1-3 read',
 'Literal vacuity (complete proof): the domain of f contains I = emptyset (0 <= |I| <= M) and f(emptyset) lies in J, so |f(emptyset)| >= D >= 2. Condition (iii) with I_2 = emptyset (always a subset of f(I_1)) gives f(emptyset) a subset of f(I) for every I. Take j_0 in f(emptyset) and J* = {j_0}; since K >= D+M > D we have ceil(K/D) >= 2 > |J*|, so (iv) demands a non-empty I with f(I) disjoint from {j_0}, which is impossible. Hence no good relation exists and the conjecture as printed is vacuously true. Intended version: the authors themselves (Heidarzadeh-Sprintson, ITW 2021, as summarised in arXiv:2202.12229 Sec. I and Remark 2; the ITW 2021 body itself was not retrieved) report that the scheme of [1] is not optimal for D=M=2 (capacity 2/ceil(K/2)). Conjecture 1 was introduced exactly to prove that scheme optimal, so under the source reduction the intended M=2 case is contradicted by the authors\' own later work. Zero credit either way.',
 'none for credit')
add(341639,['1901.07509','2202.12229'],'PARKED_AFTER_ANALYSIS_AND_RANDOM_PROBE','source Sec. V read in full (definitions, Conjecture 2, Lemma 4 proof)',
 'Reduction (proved in notes): for loopless D-graphs, mu_ext(G) = number of initial strong components (all have >= 2 nodes), and mu_int(G^T) = transversal number tau of the family {u} union Reach(u) over non-sinks u, whose minimal members are C union S with C a strong component exiting only to sinks S and |C|+|S| >= D+1. A violation needs tau*D >= K while #initial components > K/(D+1). In the natural architecture (initial 2-cycles with (D-1)-sets of sinks), this requires a (D-1)-uniform hypergraph whose private-vertex transversal number exceeds (2m+s)/D. This is impossible for D <= 4 by Tuza-type bounds and seems possible only for large D via Alon-type random hypergraphs, whose transversal lower bounds cannot be certified at checkable size. Random probe (scripts/dgraph.py): ~50,000 random loopless digraphs with K <= 10 and D in {2,3,4}; none satisfies the D-graph hypothesis (iii) at all, so the hypothesis may be vacuous for small D (not proved). Source reduction caveat: Lemma 3 actually forces hitting every feasible D-subset, which is stronger than printed condition (iii).',
 'either a proof that D-graphs have mu_ext <= floor(K/(D+1)) (possibly vacuous: no D-graphs) or an explicit large-D construction with certified transversal lower bound',
 coverage={'random digraphs':'D=2: K 3..9; D=3: K 4..10; D=4: K 5..10; about 16-19k valid samples each; 0 D-graphs','logs':'logs/dgraph-D*.log'})
add(343527,['1908.05550'],'PARKED_ASYMPTOTIC','source Sec. on Conjecture 16 read',
 'Linear-size bi-clique in the complement under an edge-density bound and no induced weak subdivision of K_t: an asymptotic (epsilon, delta n) statement with no finite certificate.',
 'general t >= 6')
add(344134,['1910.06436'],'SETTLED_BY_SOURCE','source body read (Conjecture 1.2, Theorems 1.4-1.5)',
 'Fox-Pham-Zhao Theorem 1.4 (a)+(b) (nonzero coefficients) and Theorem 1.5 (zero coefficients as free variables) prove exactly the Saad-Wolf characterization: an even-variable equation is common iff its coefficients pair up into zero-sum pairs. The source resolves the conjecture; zero credit.',
 'none')
add(344227,['1910.09999','2310.17098'],'PARKED_AFTER_EXHAUSTIVE_SMALL_SEARCH','source Sec. 1 read (Fan\'s examples, Conjecture 1.1, Theorem 1.2); K_4-minor-free resolution (Lu-Luo-Miao-Zhang, EJC 2025, arXiv:2310.17098) noted from abstract',
 'Exact search (scripts/signed6.py): all simple graphs on <= 6 vertices, every signature up to switching (spanning-forest edges positive), signed circuits = balanced circuits + both barbell types, flow-admissibility checked, exact multiplicity cover search (memoised DFS) trying k=2, then 3, then 6. Validated on Fan\'s obstructions: the three unbalanced triangles at a vertex have only even covers, and the two-triangle/two-path example has 3- and 6-covers but no 2- or 4-cover. No flow-admissible instance lacks a 6-cover.',
 'n >= 7, multigraphs and loops/half-edges not covered; general proof open',
 coverage={'n<=5':'119 flow-admissible signed instances','n=6':'3,563 flow-admissible signed instances (four chunks)','logs':'logs/signed6*.log'})
add(344586,['1911.09533','2408.13127'],'PARKED_PRE_2012_ORIGIN_AFTER_SMALL_SEARCH','source Sec. 4 read (Conjecture 4.1); Li-Qiu-Yang-Zhang arXiv:2408.13127 introduction read (Griggs 1988 Problem 3; distributive-lattice counterexamples do not cover B_n)',
 'Griggs\'s conjecture dates from 1988 (Discrete Math. 72), so it predates the 2012 rule despite the MathDB year. Exact chain-decomposition solver (scripts/chains.py; each chain holds exactly one middle-level set; DFS with dominance feasibility pruning and randomised restarts): every one of the 618 dominated sequences for n=6 is realisable. The n=7 attempt (2567 sequences) was only partial (one chunk with timeouts, no failure).',
 'n >= 7; general proof',
 coverage={'full lattice':'n <= 6 complete (n=6: 618 sequences); n=7 partial, no failures','logs':'logs/chains-full-*.log'})
add(344587,['1911.09533'],'PARKED_AFTER_EXHAUSTIVE_SEARCH','source Sec. 4 read (Conjecture 4.2 and remarks)',
 'Exact solver on B = sets of size >= n/2 (each chain contains exactly one bottom-level set, so chains are bottom set + chain above). Every dominated sequence with the stated sum is realisable for n <= 9 (n=6: 12, n=7: 16, n=8: 270, n=9: 724 sequences). Note: dominance by sigma\' is exactly the Gale-Ryser condition for level-occupancy patterns, so the difficulty is purely realisation. n=10 has 43,086 sequences, beyond lane caps. No counterexample; no proof found.',
 'general proof (realisation of Gale-Ryser level patterns by nested inclusion matchings); n >= 10 search',
 coverage={'upper half':'n <= 9 complete; n=10 not completed','logs':'logs/chains-half-*.log'})
add(346758,['2006.02603'],'PARKED_DEPENDS_ON_UNKNOWN_RAMSEY_NUMBERS','source Sec. 1 read (Theorems 1.4-1.6, Conjecture 1.7, lower-bound construction Sec. 2)',
 'MathDB paraphrase defect: the source\'s hat-K_m is the fan K_1 join P_m (K_3, K_4-e, H_12 for m=2,3,4), not "K_m with a pendant edge at each vertex". The conjectured formula agrees with the known m <= 4 values (checked: m=2 with R=6, m=3 with R=10, m=4 with R=10). For m >= 5 it is an infinite statement involving unknown R_2(F_m); no finite certificate.',
 'exact Gallai-Ramsey upper bounds for fans F_m, m >= 5')
add(347546,['2008.03253'],'PARKED_ANALYTIC_ISP_STRENGTH','source Sec. 2 read (Conjecture 2.1, Remark 2.2)',
 'Single-author conditional approach to the invariant subspace problem for quasinilpotent operators; the conjecture is analytic (spectral inclusions with an arbitrary function Phi) and, per the author, would imply the ISP for quasinilpotents. No finite route; flagship-level difficulty.',
 'n/a')
add(348515,['2010.15765','2608.25891'],'SETTLED_PUBLIC_PREPRINT_RESOLUTION','source abstract read; McGinnis arXiv:2608.25891 (v4, 3 Sep 2026; first posted 26 Aug 2026) abstract and Sec. 1 read: Conjecture 1.6 there is exactly this statement and is proved via Conjecture 1.5 (Sec. 3.2, body not checked line by line)',
 'D. McGinnis, "Multi-graded generic initial ideals, regularity, and the optimal colorful fractional Helly theorem for d-Leray complexes" proves the optimal colorful fractional Helly theorem for d-Leray complexes (a face of size >= (1-(1-alpha)^{1/(d+1)}) n_j, i.e. dimension >= that minus 1). Public resolution; zero credit.',
 'none for credit')
add(359661,['2308.13640'],'PARKED_DEEP_FLAGSHIP_TYPE','source abstract and introduction status read; web search for 2024-2026 resolutions found none',
 'Cohen-Havet-Lochet-Nisse conjecture (bounded chromatic number of strong digraphs without subdivisions of a given oriented cycle). Known for two blocks, Hamiltonian digraphs and special four-block cycles. A deep structural statement; a refutation would need an infinite family of strong digraphs of unbounded chromatic number; no finite certificate.',
 'general oriented cycles')
out={}
for k,v in sorted(E.items()):
    x=ex[str(k)]; r=rows[k]
    out[str(k)]={'mathdb_id':k,'title':x['title'],'canonical_url':r.get('canonical_url'),'source_url':x['source_url'],'first_stated_year_metadata':r.get('first_stated_year'),
      'literal_statement':x['statement'],'provenance':x['provenance'],
      'source_versions_checked':{a:abs_info.get(a,{}).get('versions') for a in v['arx'] if a in abs_info},
      'source_receipts':receipts(v['arx']),'history_check':v['hist'],
      'review_depth':v['depth'],'outcome':v['outcome'],'mechanism_and_evidence':v['mech'],'search_coverage':v['coverage'],
      'remaining_lemmas':v['remaining'],'lean':'none (no candidate endpoint; Claude lane restriction: no Lean run)','self_accepted':False,'credit':'none unless root accepts'}
assert len(out)==20 and set(map(int,out))==set(res['ids'])
(D/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n'); print('wrote',len(out))
