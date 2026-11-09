import json, hashlib, pathlib, datetime
P=pathlib.Path(__file__).resolve().parents[1]
lit={r['id']:r for r in json.load(open(P/'literal-records.json'))}
L='literal_statement_only'; PR='primary_statement_read'; PB='primary_statement_and_relevant_proof_body_read'
D={
323754:(L,'park','2–3 Lyndon transcendence basis of MZVs: implies algebraic independence results far beyond current transcendence theory; no finite or constructive route.'),
323792:(L,'park','Infinite generation/odd generators of Morita–Sakasai–Suzuki algebra E: requires graph-homology computations in all weights; no tractable mechanism identified.'),
323828:(L,'park','Kühnel–Lutz tightness implies strong minimality: open structural conjecture; no finite certificate route.'),
323832:(PB,'parked_after_search','Elder arXiv:1207.5811v1 §8.5 Conjecture 3 read; exact pseudocyclotomic search with periodicity (odd p<=15,q<=60; p<=7,q<=150) found no violation for any residue class; no proof route.'),
323834:(PB,'degenerate_literal_refutation_held_no_credit','Elder Conjecture 5 + author remark read. No violation for odd p<=15/q<=60, p<=7/q<=150, even p 4..12/q<=50. Literal domain includes p=2 where Phi~_{2,q,r}(x)=Phi~_{q,r}(-x) is always flat and the Moreover clause fails iff q≡1 mod 2w, e.g. (2,7,17), w=3. Domain-edge/trivial identity: assessed zero credit; Lean not built. See SELECTED-NOTES.md.'),
323846:(L,'park','Entropy criterion for cluster-recurrence birational maps: record status line says solved per source; analytic algebraic-entropy question, statement partially garbled; not investigated.'),
323935:(L,'park','Zhang–Liu–Wang AVD edge-colouring Delta+2 conjecture: famous open problem.'),
323978:(L,'park','Smooth splitting over Hitchin moduli space: differential-geometric, no finite route; record status line ambiguous.'),
324018:(L,'park','f(n,sqrt n)=Omega(sqrt n) (Payne–Wood): open; lower bound sqrt(n/log n) known.'),
324020:(L,'excluded_known_refuted','Fixed-collinearity n/polylog conjecture is refuted for l=3 by Balogh–Solymosi, Discrete Analysis 2018 (arXiv:1704.05089): point sets with no four collinear and largest general-position subset n^{5/6+o(1)}. Search-level confirmation; primary body not reread here.'),
324034:(L,'park','Eventual junction occupation for local-maximum disc fillings: geometric optimization statement without precise measure; not tractable.'),
324087:(L,'excluded_ill_posed','Bondage-number bound with unspecified constants c_h,c_k and o(h),o(k) terms: not a precise statement.'),
324097:(L,'park','Gyárfás–Sárközy–Selkow multicoloured matchings: general case open; no small counterexample route identified.'),
324130:(L,'park','Regularity of critical graphs with chi>=Delta=8 (Borodin–Kostochka context): open.'),
324148:(L,'park','KLS conjecture: major open problem (Klartag 2023 log bound).'),
324149:(L,'park','Variance/thin-shell conjecture: open (equivalent up to log factors to KLS progress).'),
324161:(L,'park','Boundary Colin de Verdière for Steklov multiplicity: spectral geometry, no finite route.'),
324192:(L,'park','Geometric limit of largest family sizes in critical splitting trees: probabilistic limit theorem; not investigated.'),
324315:(L,'park','Coisotropic orbit characterization: statement garbled (identity missing in record); not tractable without source restoration.'),
324335:(L,'park','Partial symmetries n=3 rank 5/decomposability: definitions not restored; not investigated.'),
324342:(PB,'CANDIDATE_full_literal_Lean_refutation','Etzion–Vardy–Yaakobi Conjecture 5 (arXiv:1210.5725 v1/v2; ISIT13 Conj.1) REFUTED: Goethals–Seidel skew conference matrix W of order 20 has F_19 row code [20,10,9] (MDS would need d=11). Lean: conjecture5_false : ¬Conjecture5, axioms propext/Classical.choice/Quot.sound, clean rebuild + leanchecker rc0. Paley case shown MDS via extended Reed–Solomon (context, not claimed). See conference/PROOF.md.'),
324442:(L,'park','Wilfong–Haxell–Winkler delay colouring: open beyond d=3.'),
324470:(L,'excluded_ill_posed','"number of cycles is related to the bridge number": no precise formula stated.'),
324487:(PR,'excluded_known_large_n','Kühn–Lapinskas–Osthus Conjecture 2 proved for all large n by Csaba–Kühn–Lo–Osthus–Treglown (Memoirs AMS 2016), as stated in the source itself; residual small n has astronomically large threshold, no route.'),
324488:(PR,'park','Kühn–Lapinskas–Osthus Conjecture 6 (graph-by-graph): open; proved only for delta>=(2-sqrt2+eps)n.'),
324518:(PB,'excluded_refuted_by_source_data','Buck–Dolzhenko–Jonoska–Saito–Valencia Conjecture 5.7 is contradicted by the source\'s own Table (v1 line 194; EJC 22(3) P3.43 Table 1): {3} in GR_6 and GR_2={{0},{1}}, so under Definition 2.6 order the maximum ranges for 2 and 6 vertices are [1,1],[3,3]; published version drops the conjecture.'),
324529:(L,'park','Kadec–Pełczyński dichotomy for JBW*-triple preduals: functional analysis, not investigated.'),
324531:(L,'park','Liu–Wang–Zhang ndi<=Delta+2 (equivalent family to AVD conjecture): open.'),
324532:(L,'park','Baril–Togni multigraph ndi bound: open; not investigated.'),
324537:(L,'park','Total edge irregularity strength (Ivančo–Jendrol\' type) conjecture: open in general.'),
324570:(PB,'partial_ordinary_no_credit','Arratia–DeSalvo Conjecture 1 (sup D<1; still open in AAP 2015 published version, 0 OpenAlex citers) proved: D(p)<=1-c0, c0=0.34432 via Poissonization and (1+x)e^{-x}>=e^{-x^2/2}. MathDB literal adds attainment of a global maximum (not in source; doubtful) - unresolved, so not full scope. No Lean.'),
324701:(PB,'parked_after_search','HLP Conjecture 1.1 read with Prop 5.2. SAT search (CaDiCaL) over all <=7-vertex connected Delta>=3 graphs and all cubic graphs on 8,10 vertices, m=3, n=4..7: only the prism fails; m=5 atlas run reported in SUMMARY.'),
324750:(PB,'excluded_known','Guo Conjecture 12 proved by Lu–Guo, arXiv:1503.07226 Theorem 2 (under Assumption 1, the standing setting of the source).'),
324778:(L,'park','Bollobás–Erdős properly coloured Hamilton cycle: asymptotic version known (Lo); exact open.'),
324779:(L,'park','Clozel higher-homology formula: representation theory; not investigated.'),
324788:(PB,'excluded_known_in_source','Boussaïri–Ille arXiv:1301.1157 abstract/intro: "We answer the conjecture positively" (Brignall Conjecture 3.8).'),
324793:(L,'park','Narkiewicz N_1(G) formula: open beyond known group classes.'),
324810:(L,'park','Consecutive-layer pi^c(P)=e(P): open extremal poset problem.'),
324821:(L,'excluded_known_refuted','Polynomial Alon–Saks–Seymour refuted by Göös (ECCC TR15-012 / FOCS 2015), superpolynomial separation.'),
324822:(L,'excluded_known_corollary','Oriented version: bp_or(G)<=bp(G) (orient each biclique of a partition), so Göös\' superpolynomial chi vs bp separation refutes it; routine corollary of known result.'),
}
assert set(D)==set(lit), set(lit)^set(D)
out={}
for i in sorted(lit):
    r=lit[i]; rec=r['record']; depth,disp,note=D[i]
    out[str(i)]={'title':rec['title'],'canonical_url':rec['canonical_url'],'source_url':rec['source_url'],
      'corpus_chunk':r['chunk'],'corpus_line':r['line'],'chunk_sha256':r['chunk_sha256'],'line_sha256':r['line_sha256'],
      'review_depth':depth,'disposition':disp,'note':note,'accepted_credit':0}
json.dump(out,open(P/'results.json','w'),indent=1,ensure_ascii=False)
import collections; print(collections.Counter(v['review_depth'] for v in out.values())); print(collections.Counter(v['disposition'] for v in out.values()))
