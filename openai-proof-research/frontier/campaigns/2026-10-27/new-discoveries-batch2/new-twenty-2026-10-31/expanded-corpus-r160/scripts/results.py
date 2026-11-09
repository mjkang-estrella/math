import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
intake=json.loads((L/'outputs/intake.json').read_text())
absinfo=json.loads((L/'outputs/abs-info.json').read_text())
rec=json.loads((L/'outputs/fetch-receipts.json').read_text())
EXTRA={'353800':['green-1605.07263','ls-2212.12754','f2-2510.27573','gen-2609.12499','vdc-2510.27581','search-sarkozy-ff','search-sarkozy-poly','search-naslund','search-li-sauermann','search-kth-power-diff','search-sarkozy-all','search-sarkozy-all2','search-le-liu','search-le-liu2','search-le-hoang','openai-squarediff','oai-psq-readme','oai-psq-intro','oai-psq-bib','omega-head','openai-head','omega-root','omega-D5','omega-Problems'],
 '354435':['kkp-1308.0611','bdfl-1511.04569','search-123-hyper','search-twinfree','search-kkp','search-bdfl'],
 '382216':['qzf-2509.03967','search-qzf'],'382075':['search-fs'],
 '354851':['search-o2'],'355576':['search-blowup'],'354661':['search-arr'],'354875':['search-thrackle']}
def receipts_for(k):
    ids=set(EXTRA.get(str(k),[]))
    return [ {x:r.get(x) for x in ('id','url','status','sha256','bytes','file','utc','error') if x in r} for r in rec if str(r['id']).split('-')[0]==str(k) or str(r['id'])==str(k) or r['id'] in ids]
D={}
def put(k,**kw): D[str(k)]=kw
put(353486,outcome='parked_structural',review_depth='MathDB statement; arXiv abs (current v5, 8 Jun 2023, 69 pp.); no body read',
 summary='Barnette-type conjecture on rounded 1-factors in planar sink-regular (3,4)-bipartite digraphs (Abdi-Cornuejols-Zlatin). Infinite structural statement whose objects (rounded 1-factors, bases of M_1(D,1)) need the 69-page source machinery; no finite certificate mechanism identified; it would imply a planar tau=3 case of Woodall-type packing.',
 computations='none', remaining='A proof or a counterexample requires the source definitions of rounded 1-factors and dc(J); not attempted.')
put(353553,outcome='source_resolved_zero_credit',review_depth='MathDB statement; arXiv abs current v2 (Adv. Appl. Math. 148 (2023) 102532)',
 summary='The MathDB source (W. Fang, arXiv:2202.03542) itself SETTLES the Zeilberger-Reed conjecture: abstract "we settle this conjecture by giving a direct bijection" between 3-connected planar linear normal lambda-terms and bipartite planar maps. MathDB text ("supplied source gives no resolution status") is defective.',
 computations='none needed', remaining='none (known result)')
put(353800,outcome='CANDIDATE_counterexample',review_depth='Full source LaTeX v3 read (Sections 1-3, all proofs, Conjecture 13 and its context); Green 2017 LaTeX read; four later papers grepped; registries path-screened at live HEADs',
 summary='Naslund Conjecture 13 (k=2, q odd: Theorem 1 tight, max |A| = q^{3n/4}) is FALSE. Explicit witness: A in P_{5,4} with |A|=160 > 125 = 5^{4(1-1/4)} and no square differences, verified by two independent scripts; Lean draft (UNCOMPILED) uses it. Uniform disproof (Theorem U plus Theorem 3 in CANDIDATE-353800.md): for every prime power q = 1 mod 4 and every n = 0 mod 4 there is a square-difference-free A with |A| = q^{3n/4}(1+1/q+2/q^2). The slice is the level set {4xz-y^2 = nonsquare} (independent because tangent planes are anisotropic) plus one or two square multiples of each isotropic line. Also fails at q=3 for every n = 0 mod 4, n>=8 (computational slice 297 > 243). For q = 3 mod 4 and n = 4 the bound is exact (Hoffman). Exponent 3/4 untouched.',
 computations='Theorem U checked for q=5,13,17,29,37,41 (0 violations); ILS slices q=5 -> 32, q=9 -> 99, q=13 -> 209, q=17 -> 311, q=3 n=8 -> 297; full verification of q=5 n=8 (|A|=20000 > 15625); k=3 q=7 n=6 -> 637 (< 656.1); k=4 q=5 n=8 -> 1100 (< 1397.5); k=3 q=4 n=6 exact 1280 < 1625.5; exact q=3 n=4 alpha=9; Hoffman q=3,7 exact q^2; q=5 optimum in [32,42], not proved.',
 remaining='Root/Sol: compile lean/MathDB353800.lean (UNCOMPILED) and audit axioms; independent review of novelty (unread: Le-Liu 2013 Acta Arith.; Link 2008 manuscript; symmetric-bilinear-forms association-scheme literature).',
 candidate_file='CANDIDATE-353800.md', lean_draft='lean/MathDB353800.lean (UNCOMPILED)')
put(353973,outcome='source_resolved_zero_credit',review_depth='MathDB statement; arXiv abs (v1 only)',
 summary='Defective MathDB record: the source (A. Bickle, "Plane triangulations without spanning 2-trees", arXiv:2203.10239) ANSWERS Cai\'s question in the NEGATIVE by an infinite class of maximal planar graphs with no spanning 2-tree. The printed "conjecture" (every maximal planar graph has a spanning 2-tree) is refuted in the source itself.',
 computations='none needed', remaining='none')
put(353989,outcome='parked_open_large_instances',review_depth='Source LaTeX read (Section 1 statements, Prop. on three-cycle cases, Remark 1.5 and ancillary sage)',
 summary='Only r = 3 is open; source proves it unless all three lengths have equal parity, none has length 2 and no pair product is hamiltonian. Smallest open instance is C3xC5xC7 (105 vertices, out-degree 3). A counterexample would need a nonexistence proof for two arc-disjoint hamiltonian paths at >= 105 vertices; existence checks only confirm instances. No finite route.',
 computations='none', remaining='Constructive proof for pairwise-coprime odd lengths, or a large exhaustive nonexistence certificate (solver work, not allowed in this lane).')
put(354435,outcome='parked_bounded_search_with_attribution_defect',review_depth='Source LaTeX read (definitions; hypergraph section conjecture); original KKP arXiv:1308.0611 LaTeX read; BDFL 1511.04569 fetched',
 summary='The source attributes to Kalkowski-Karonski-Pfender "no twin-free hypergraph in B^r" for every r >= 3. KKP actually conjecture this only "for large enough r" (1308.0611, conjecture after the BenDFH construction). A small r = 3 counterexample would refute only the misquoted version. Exhaustive and random searches found none.',
 computations='All labelled twin-free 3-uniform hypergraphs on <= 6 vertices (2^20 edge sets; 1,045,380 twin-free tested at n=6, 918 at n=5): every one has a {1,2}-weighting with no monochromatic-sum edge. Random samples n=7 (175,993), n=8 (54,883), n=9 (18,701); random d-regular (d=2,3,4) twin-free 3-graphs n=6..18: 842,398 tested; no counterexample.',
 remaining='Structured search for sparse near-regular twin-free 3-graphs beyond n=6; r >= 4 not searched.')
put(354500,outcome='defective_statement_zero_credit',review_depth='Source LaTeX v3 read (final-remarks subsection ss:finrem-GP-injection: graph G and conjecture; section s:restricted: tau_i, delta operator definitions)',
 summary='Chan-Pak-Panova matching conjecture is false for a trivial reason. In every edge (pi,sigma)-(pi\',sigma\'), y lies before x in pi\' and after x in sigma\', so no W-vertex is adjacent to a diagonal pair (tau,tau) in V. Hence a W-saturating matching needs N_{a-1}N_{a+1} <= N_a^2 - N_a. That fails at every Stanley equality case with N_a > 0, e.g. the 3-element antichain (x, a=2: |W|=4, only 2 reachable V-vertices). This contradicts the source\'s own (equality-case) context; zero-credit defect.',
 computations='All naturally labelled posets n=3,4,5: matching saturating W fails in 3/6, 86/118, 1999/2281 (x,a) instances.',
 remaining='none (defect); a repaired graph definition would be a different question.')
put(354575,outcome='parked_structural',review_depth='MathDB statement; arXiv abs current v2 (21 Aug 2024)',
 summary='Hasanvand: k-edge-connected (k >= 4) graphs have spanning closed trails meeting each v at most ceil((d(v)-2)/k)+1 times. Infinite structural statement; small instances verify only; no certificate route.',
 computations='none', remaining='proof from the source decomposition theorem; not attempted.')
put(354578,outcome='source_internal_contradiction_zero_credit',review_depth='Full source LaTeX v4 read',
 summary='Path-energy Conjecture 2 (k 2-connected components -> exactly k positive path eigenvalues) already fails at k = 1, and the source\'s own Table 1 entry for K_{p,q} shows this. The quotient eigenvalues (p(q-1)+q(p-1) +- sqrt((p-q)^2+4p^3q))/2 are both positive once q > (p^2+p-1)/(p-1), e.g. K_{2,6}, contradicting its caption and Conjecture 1. The 1-positive-eigenvalue conjecture is refuted by the source data; zero credit.',
 computations='Exact char-poly + Descartes census of all connected graphs n <= 7: the 2-connected graphs with 2 positive path eigenvalues at n=7 are K_{1,1,5} and FQjVo; bowtie (n=5, 2 blocks) has 1 positive eigenvalue; K_{2,6}, K_{2,7}, K_{3,7}, K_{3,8}, K_{1,1,t} (t>=5) have 2.',
 remaining='none')
put(354661,outcome='parked_structural',review_depth='MathDB statement; arXiv abs (v1); arXiv search',
 summary='Existence of an INFINITE family of 4-edge-critical simple pseudocircle arrangement graphs; needs a construction proof, not a finite certificate. No later resolution found (arXiv search 2026-11-04).', computations='none', remaining='construction')
put(354851,outcome='parked_asymptotic',review_depth='MathDB statement; arXiv abs current v5 (JCTB 2024)',
 summary='Le\'s conjecture: O_2-free n-vertex graphs have at most n^c induced paths; asymptotic polynomial bound, excluded by reserve7 cues (no finite certificate).', computations='none', remaining='n/a')
put(354875,outcome='parked_geometric',review_depth='MathDB statement; arXiv abs current v6 (DMTCS 2025)',
 summary='Strengthened thrackle conjecture for topological trees (m <= n); deep topological-geometric statement strengthening the thrackle conjecture; no finite route.', computations='none', remaining='n/a')
put(355102,outcome='parked_structural',review_depth='Source LaTeX read (Conjectures 1.4-1.6 and conclusion)',
 summary='Weakest rainbow-basis covering conjecture (exists k: every k-base matroid with 2-bounded partition is covered by k bases one rainbow). Existential-in-k matroid statement; no finite certificate.', computations='none', remaining='n/a')
put(355218,outcome='parked_bounded_evidence',review_depth='Source LaTeX read (Definitions, Section 7, Conjectures 7.5/7.6); prior campaign note middle-review-r1 read',
 summary='gamma~c(L(G)) <= gamma~c(M(G)). Reduction: disjoint unions reduce to connected components (OCD sets of unions must contain whole components), so connected G suffice. Prior lane middle-review-r1 found no counterexample for connected n <= 8 (except K2 under the empty-complement convention B). Proof attempt: replacing each vertex of an OCD set S of M(G) by an incident edge yields an L(G)-dominating set of size <= |S|, but connectivity of E \\ S\' can fail; no fix found.',
 computations='none new (prior n<=8 probe reused by citation)', remaining='Connectivity-preserving choice of replacement edges (main lemma).')
put(355576,outcome='parked_analytic',review_depth='MathDB statement; arXiv abs current v3',
 summary='Common blow-up conjecture (asymptotic homomorphism-density commonness); analytic; excluded by reserve7 cues.', computations='none', remaining='n/a')
put(357115,outcome='parked_structural',review_depth='Source LaTeX read (introduction, Conjectures)',
 summary='(k+2)-colourability for girth-(2l+1) graphs with k odd-hole lengths (R. Chen). k=1 case is the Wu-Xu-Xu conjecture, proved for l=2,3 and l>=5; general k open; counterexamples would need >= 21-vertex girth-5 high-chromatic graphs; no finite route.', computations='none', remaining='n/a')
put(357777,outcome='source_resolved_zero_credit',review_depth='MathDB statement; arXiv abs current v2',
 summary='The MathDB source (Xu-Li-Zhou, arXiv:2303.09741) CONFIRMS Shi-Shan\'s conjecture: abstract "In this paper, we confirm the conjecture". Known result.', computations='none', remaining='none')
put(361080,outcome='parked_structural',review_depth='Source LaTeX read (statements; Section 3 structure)',
 summary='BMMN cycles 0 mod k conjecture; source proves k=3 and (k+1)-critical graphs with minimum degree k; open part is (k+1)-critical graphs with minimum degree >= k+1 for k >= 4; infinite structural.', computations='none', remaining='counting cycles 0 mod k in (k+1)-critical graphs with delta >= k+1')
put(382075,outcome='known_result_zero_credit',review_depth='Source LaTeX read (Conjecture 5.2); H. Zhu arXiv:2307.08121v3 (Annals of Combinatorics 2024) LaTeX read: Theorem on exactly two components',
 summary='Wang-Lu-Chen two-component conjecture is the k = 2 case of Zhu Theorem 1.5 (connected bipartite non-cycle X, n >= 5, n >= 2k: FS(X,K_{k,n-k}) has exactly two components iff no k-bridge and X not T6,T7,T8; T6-T8 contain non-trivial cut edges). FS(X,Y) is isomorphic to FS(Y,X). Known.',
 computations='Independent check: all qualifying Y for n=5,6,7 (40), n=8 (120), n=9 (first 288 qualifying graphs, graph9c lines 0-12339): exactly 2 components each.', remaining='none')
put(382216,outcome='parked_open_verified_small',review_depth='Full source LaTeX read (game definition in Introduction; Cartesian-product subsection: conjecture and bounds); Abiad-Moghaddas arXiv:2509.03967 grepped; registries path-screened',
 summary='Conjecture Z_q(K_{n,m} box K_2) = 2min(n,m) (q=0), n+m (q>=1). Source proves Z_0 <= 2min, n+m-1 <= Z_q <= n+m. Exact minimax solver (validated on the source K_{n,m} and book-graph values) confirms the conjecture for all n,m >= 2 with n+m <= 10 (q=0,1; q=2 for n+m <= 9; all q>=1 follow by monotonicity and Z <= n+m). No later resolution found. A proof needs an oracle strategy for Z_1 >= n+m and the PSD lower bound Z_0 >= 2min(n,m) for all n,m; Lean would require formalizing the two-player game. High Lean cost; parked.',
 computations='outputs/qzf-run1..4.log', remaining='Z_1(K_{n,m} box K_2) >= n+m for all n,m (oracle strategy); Z_+(K_{n,m} box K_2) >= 2min(n,m).')
out={}
for k in json.loads((L/'reservation.json').read_text())['ids']:
    i=intake[str(k)]; r=i['record']
    e=dict(mathdb_id=k,title=r['title'],canonical_url=r['canonical_url'],source_url=r['source_url'],
      raw={'chunk':i['chunk'].split('/new-discoveries-batch2/')[-1],'line':i['line'],'raw_sha256':i['raw_sha256'],'chunk_sha256':i['chunk_sha256'],
           'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'raw_copy':f'sources/{k}.raw.jsonl'},
      arxiv_current=absinfo.get(str(k),{}).get('versions'), journal_ref=absinfo.get(str(k),{}).get('jref'),
      historical_check='No prior campaign note except 355218 (middle-review-r1 n<=8 probe) found by scoped grep of new-twenty-2026-10-31 and new-discoveries-batch2/lanes (*.json,*.md,*.jsonl).',
      receipts=receipts_for(k))
    e.update(D[str(k)]); out[str(k)]=e
assert len(out)==20
(L/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False))
print('wrote',len(out)); print({k:v['outcome'] for k,v in out.items()})
