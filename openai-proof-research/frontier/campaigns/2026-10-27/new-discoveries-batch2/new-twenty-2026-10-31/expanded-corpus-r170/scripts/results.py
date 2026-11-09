import json,pathlib,datetime,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'extracted.json').read_text())
rec={r['id']:r for r in json.loads((L/'outputs/fetch-receipts.json').read_text()) if 'sha256' in r}
def src(i):
    out={}
    for k in (f'{i}-abs',f'eprint/{i}'):
        if k in rec: out[k]={'url':rec[k]['url'],'sha256':rec[k]['sha256'],'utc':rec[k]['utc']}
    return out
D={
'358956':dict(outcome='SETTLED_PRIOR_REFUTATION',review_depth='full source TeX read (Section "A conjecture", Thm w2alpha, Thm w2shed, W_k definition); exhaustive computation; primary prior-art abstract read',
 summary='Conjecture is equivalent to "(2) implies well-covered" (direction (1)=>(2) holds via the source theorem since W2 is a subclass of well-covered). Exhaustive search of all connected graphs up to 10 vertices (1..9 from graph{n}c.g6, all 11,716,571 from graph10c.g6.gz) found exactly one mismatch, ICOf~z}~O = 3K2 join 2K2 (maximal independent sets of sizes 3 and 2; every private-neighbour set is the matching partner). The family sK2 join tK2 (s!=t, s,t>=2) refutes the conjecture, but this exact construction is published: Feghali and Marin, "Three remarks on W2 graphs", arXiv:2307.15573 (v1 July 2023, v2 Nov 2023; Theoretical Computer Science 2024). Zero credit.',
 prior_art=['https://arxiv.org/abs/2307.15573 (receipt outputs/fetch-receipts.json id prior/2307.15573-abs)'],
 computation='scripts/w2.py, scripts/w2_gz.py, scripts/w2_selftest.py, scripts/w2_analyze.py; counts: connected W2 graphs n=2..10: 1,1,1,2,5,16,82,451,3691; unique mismatch at n=10'),
'370752':dict(outcome='PARKED_OPEN_BOUNDED_SEARCH',review_depth='full source TeX read (Conjecture con:infinite, Obs. infinity, Thm pendant-path, Thm strong-torus-infinity and proofs)',
 summary='Source reduces to d<p<2d and proves it for H with a (d,p)-close vertex, paths, pendant paths, and C_m x C_n. Exact bitset backtracking (scripts/dp.py) found no counterexample in: all bad connected G<=8 vertices with diam>=p+1 x connected H<=9 vertices without close vertex for (d,p)=(2,3); bad cycles and bad small G x cycles C_8..C_24, McGee, Tutte-Coxeter, Q4, 6x6 torus for (2,3),(3,4),(3,5),(4,5),(4,6),(4,7) (some node-cap timeouts recorded in logs); all pairs of 4-regular circulants C_n(1,a), n<=26 (bad x bad/good), 929 products, exact, (2,3). New (unpublished, zero-credit) local arguments: if the maximum p-packing of C_m has size 1, or size 2 with 3d<=2p, then gamma_d^p(C_m x H)=infinity for EVERY graph H (radius-(p-d) balls carry at most one label, forcing occupied H-vertices into a (2r)-packing that contradicts domination at an occupied vertex). Surviving cycle regimes (e.g. (5,7) with C_23) would need huge large-girth H. No finite certificate found.',
 computation='scripts/dp.py, dp_sweep.py, dp_girth.py, dp_regular.py, dp_sweep2.py, dp_circ.py; logs/dp-circ-2-3.log'),
'371290':dict(outcome='PARKED_OPEN_BOUNDED_SEARCH',review_depth='full source TeX read (definitions Sec.2-3, Prop. cycle, Prop. subcubic, concluding conjecture)',
 summary='Literal "G != C5" is refuted only by disconnected graphs with a C5 component (wording defect, zero credit; source Prop. subcubic uses "no component isomorphic to C5"). Connected search: every connected nice graph on <=8 vertices except C5 has a QM-NSD 4-edge-colouring; all connected 9-vertex graphs with min degree >=3 and Delta>=4 (84,242) and min degree 2 up to index 36824; all connected 10-vertex graphs with min degree >=4 (1,249,972); circulants C_n(S), n<=16, |S|<=4, and C5-based lexicographic/strong/Cartesian products: all 4-colourable. Checker reproduces source values for cycles and K5.',
 computation='scripts/qm.py, qm_struct.py, qm_filter.py'),
'334658':dict(outcome='PARKED_OPEN_BOUNDED_SEARCH',review_depth='source TeX read (Conjecture conj:upperbound, Thm PetrosyanMkhit, Delta<=4 theorem); web status check',
 summary='Exhaustive search for cyclic interval t-colourings with t>|V|: part (i) all connected triangle-free graphs with Delta>=5 on <=9 vertices (t in (n, min(m,n+Delta-3)]) - none; 10 vertices only indices 0..15840 of graph10c with node-cap timeouts (partial). Part (ii) all connected graphs <=6 vertices, 7 vertices all but 22 dense graphs (node cap). Checker reproduces W_c(C_n)=n and W_c(K_{a,b})=a+b. No counterexample.',
 computation='scripts/cyc.py, cyc10.py; logs/cyc-*.log'),
'330625':dict(outcome='SETTLED_PROVED',review_depth='source TeX extracted; web prior-art check',summary='Ker-diadem inequality |ker G|+|diadem G|<=2alpha(G) proved by T. Short (Electron. J. Combin. 23(2) 2016, P2.43); short proof arXiv:1701.03040; strengthening arXiv:2603.10316. Zero credit.'),
'329573':dict(outcome='SETTLED_PRIOR_REFUTATION',review_depth='source TeX read (Conjecture in conclusions); Alon-Kupavskii PDF read (Thm 1.1, remark on Erdos-Simonovits and Maehara)',
 summary='dim(G)<=2chi(G) for faithful Euclidean dimension is false: Alon-Kupavskii "Two notions of unit distance graphs" (JCTA 2014, manuscript Feb 2014) Thm 1.1(2): K_{d,d} minus a matching of size d-3 is not a faithful distance graph in R^d (d>=4); with d=5 a bipartite graph has dim>=6>4=2chi. Earlier constructions: Erdos-Simonovits (Ars Combin. 9, 1980) Prop. 1, Maehara (DCG 4, 1989). Zero credit.',
 prior_art=['https://web.math.princeton.edu/~nalon/PDFS/ramsey10.pdf (receipt prior/alon-kupavskii-two-notions)']),
'330517':dict(outcome='SETTLED_PRIOR_REFUTATION',review_depth='abstract and MathDB statement',summary='Brualdi-Massey incidence colouring conjecture chi_i<=Delta+2 is false (Guiduli 1997, Paley graphs); the MathDB record and source abstract say so. Zero credit.'),
'344558':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Linear arboricity conjecture (Akiyama-Exoo-Harary); open in general, asymptotic results only (Lang-Postle). Source arXiv:1911.08397 is about the path partition conjecture. No finite route.'),
'330309':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Equitable total colouring conjecture (Fu/Wang) implies the Total Colouring Conjecture; open. No finite route beyond known small-graph verifications.'),
'328966':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Acyclic edge colouring conjecture a\'(G)<=Delta+2 (Fiamcik; Alon-Sudakov-Zaks); open. Source is the Local Action Lemma paper.'),
'323109':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Same acyclic edge colouring conjecture (duplicate of 328966); source proves mad<4 case. Open.'),
'366150':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Burris-Schelp conjecture chi\'_vd in {pi, pi+1}; open in general (lower bound trivial). Source handles regular graphs.'),
'368238':dict(outcome='PARKED_OPEN',review_depth='source TeX skimmed (intro, conjectures, results for Delta<=6)',summary='Multiset 1-2 conjecture introduced by the source (2025); holds for Delta<=3, complete, 3-colourable and Delta<=6 cases per source; equivalent to the sum version on equal-degree edges. No finite lead.'),
'324533':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Total 1-2 conjecture (Przybylo-Wozniak 2010); open, chi^t<=3 known (Kalkowski; Keusch).'),
'324536':dict(outcome='PARKED_OPEN_BOUNDED_SEARCH',review_depth='abstract; web status check',summary='Additive colouring conjecture eta(G)<=chi(G) open (bipartite case open). Exhaustive check: all connected graphs <=8 vertices and all connected bipartite graphs with 9 (730) and 10 (4032) vertices satisfy it.',computation='scripts/lucky.py'),
'352331':dict(outcome='PARKED_HARD',review_depth='abstract',summary='ZFC realization of Ext-graphs (Herden question); set-theoretic, consistency result under GCH in source. Not finite.'),
'335703':dict(outcome='PARKED_HARD',review_depth='abstract; web check',summary='Bounded geodecity of subdivisions (Weissauer, Steiner trees and higher geodecity); qualitative structural conjecture, no finite certificate route.'),
'333481':dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Narrowness conjecture, equivalent to Erdos-Hajnal (Fox). Famous; not finite.'),
'333717':dict(outcome='PARKED_OPEN',review_depth='abstract; web status check',summary='Deficiency def(G)<=|V(G)| (Bouchard-Hertz-Desaulniers); still open per 2026 arXiv:2609.15873; verified for tripartite graphs <=10 vertices (2025). Deficiency is hard to compute exactly; no tractable route.'),
'331997':dict(outcome='PARKED_HARD',review_depth='MathDB statement only',summary='Strong geometric description of non-parallelizable tensegrities; vague algebraic-geometric existence conjecture; no finite route.'),
}
res={}
for i in json.loads((L/'reservation.json').read_text())['ids']:
    k=str(i); e=ex[k]
    res[k]=dict(mathdb_id=i,title=e['title'],source_url=e['source_url'],provenance=e['provenance'],source_receipts=src(k),**D[k],credit_claim='none')
(L/'results.json').write_text(json.dumps(res,indent=1,ensure_ascii=False)+'\n')
print(len(res))
