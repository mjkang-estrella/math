"""Assemble results.json (20 ID-keyed entries) and artifact-hashes.json.  Usage: finalize.py LANE"""
import sys, json, pathlib, hashlib
D = pathlib.Path(sys.argv[1]).resolve(); S = D / 'sources'
ex = json.loads((D / 'extracted.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def rc(*names):
    out = []
    for n in names:
        r = json.loads((S / (n + '.receipt.json')).read_text())
        out.append({'file': 'sources/' + n, 'url': r['url'], 'utc': r['utc'], 'status': r.get('status'), 'sha256': r.get('sha256'), 'bytes': r.get('bytes')})
    return out
NO_LEAN = 'No Lean run (Claude-lane restriction); no Lean packet.'
E = {
 '349986': dict(outcome='parked_deep_out_of_scope', review_depth='arXiv abstract and version history (v1, v2) of 2103.02757',
   receipts=rc('2103.02757-abs.html'),
   disposition='Zapletal proves consistency (relative to an inaccessible) of ZF+DC with chi(G3) countable and chi(G4) uncountable; the n>=4 analogue is a forcing/consistency statement with no finite certificate. Not attempted.'),
 '350085': dict(outcome='parked_deep', review_depth='arXiv abstract and versions (v1-v3; v2 only author-name fixes) of 2103.07886',
   receipts=rc('2103.07886-abs.html'),
   disposition='Heroic-set conjecture (Gyarfas-Sumner analogue for dichromatic number) is a deep structural statement; the only-if direction is prior work; a counterexample needs a family of unbounded dichromatic number, not a finite object. Disposed quickly per brief.'),
 '350166': dict(outcome='parked_deep_out_of_scope', review_depth='arXiv abstract of 2103.12285 (single version)', receipts=rc('2103.12285-abs.html'),
   disposition='Generic existence of WKB cameral networks over the Hitchin base: analytic/geometric, no finite route.'),
 '350189': dict(outcome='parked_open_statement_status_defect', review_depth='2103.13359 v3 body section 1 and 4 read (connectedness passage pp.3-4, Theorem 5)',
   receipts=rc('2103.13359-abs.html', '2103.13359.pdf'),
   disposition='MathDB marks this solved, but the source (Groenland-Johnston-Scott-Tan, v3 2023) proves only l >= 9n/10 and calls the floor(n/2)+1 threshold a belief of Spinoza and West; no later proof found by search. Instances n=6 (Manvel, (n-2)-deck) and n=7,8 (Kostochka-Nahvi-West-Zirlin, (n-3)-deck for n>=7) are theorem-covered; the first open instance is n=9, l=5. An exhaustive comparison of the 5-decks of all 274,668 nine-vertex graphs is not feasible in pure Python within the lane caps (no numpy available); not run. Sharpness is shown by the printed P_n vs C_{ceil(n/2)+1}+P_{floor(n/2)-1} example.',
   search_coverage='none beyond theorem-covered n <= 8'),
 '350311': dict(outcome='parked_ill_posed', review_depth='arXiv abstract; MathDB statement itself says no precise family is given',
   receipts=rc('2104.02296-abs.html'),
   disposition='"There is a nice infinite forbidden-subdiagram characterization" names no family; not a precise mathematical statement, so no exact solution is possible. Sibling 350308 was handled by r121.'),
 '350420': dict(outcome='parked_open', review_depth='2104.07416 v3 sections 6-7 (Theorem 6.1(i), Lemma 6.4, Conjecture 7.1); 2306.08052 introduction; 2409.05678 abstract',
   receipts=rc('2104.07416-abs.html', '2104.07416.pdf', '2306.08052-abs.html', '2306.08052.pdf', '2409.05678-abs.html'),
   disposition='Known: 3p^2+p+1 <= omega_a <= omega_r <= 42p^2-11 (p=2m+n, 2m+n>=3); the absolute equality was settled by Bandopadhyay-Sen-Taruni (arXiv:2409.05678); the relative equality remains open. The literal statement also covers (m,n)=(0,1), where the relative clique number of planar simple graphs is 4, not 5: a zero-credit smallest-parameter correction, not pursued. A counterexample would need a planar (m,n)-graph with a relative clique above 3p^2+p+1; no tractable finite search.'),
 '350421': dict(outcome='EXCLUDED_KNOWN_RESOLUTION', review_depth='2306.08052 v2 abstract and introduction (Conjecture 1.5 and its resolution) read',
   receipts=rc('2104.07416-abs.html', '2104.07416.pdf', '2306.08052-abs.html', '2306.08052.pdf'),
   disposition='Settled by Nandi-Sen-Taruni, arXiv:2306.08052 (v2 Oct 2023): omega_r(n,m)(P4) <= 2(2n+m)^2+2 with tight examples for (n,m) != (0,1). The literal (0,1) case fails (value 2, not 4): a zero-credit endpoint correction.'),
 '350432': dict(outcome='CANDIDATE_full_proof', review_depth='entire 2104.07852 v1 read (definitions, Lemma 5, Theorems 18, 19, 25, Corollaries 23, 24, 26, Theorems 27, 28, Section 7); thesis (2023) Section 3.4; 2203.04953 text screened',
   receipts=rc('2104.07852-abs.html', '2104.07852.pdf', '2203.04953-abs.html', '2203.04953.pdf', 'cm-thesis-0837616.pdf', 'cm-thesis-0781733.pdf'),
   disposition='Full proof that for 1<=i<=c-2<=k the unique obstruction of type (c,i) is iK1+(c-i-1)K2+X with X = K_{i,i} (c=k+2), coK2 (+) (K2+iK1) (c=k+1), K1 (+) ((k-c+2)K2+iK1) (c<=k). See CANDIDATE.md. Still open in the 2023 thesis (Conjecture 3.27).',
   search_coverage='all cographs of order <= 12 for k <= 6; all iK1+tK2+H with H connected of order <= 10 for k <= 7 (0 mismatches); lemma checks 38,736 instances',
   lean='UNCOMPILED draft statement in lean-draft/PolarUniqueness.lean (contains sorry; plan only). Lean cost high (component bookkeeping and isomorphism normal form).',
   risk='elementary three-page proof; root must judge it against the short source-ingredient precedents. It does not use the source Theorem 25 or Corollary 26.'),
 '350476': dict(outcome='EXCLUDED_KNOWN_RESOLUTION', review_depth='2104.10080 v2 main theorem statement (Theorem with item (iv)) and conjecture paragraph read',
   receipts=rc('2104.10080-abs.html', '2104.10080.pdf'),
   disposition='Proved in its own source: Ng, Discrete Math. 344(12) (2021) 112605, I(C_n) = {C_n, D_n} for odd n >= 5 except n = 9, 15 (both divisible by 3), which covers every odd n >= 5 with 3 not dividing n.'),
 '350599': dict(outcome='parked_deep', review_depth='arXiv abstract of 2105.02056', receipts=rc('2105.02056-abs.html'),
   disposition='Graph-complex cohomology and elliptic GRT Lie algebra; no finite certificate route.'),
 '350643': dict(outcome='parked_deep', review_depth='arXiv abstract and versions of 2105.04237 (EPTCS 372)', receipts=rc('2105.04237-abs.html'),
   disposition='Decidability of the word problem for Gray categories; unknot-hard; deep, no finite route.'),
 '350663': dict(outcome='parked_analytic', review_depth='arXiv abstract and versions v1-v3 (2026 erratum v3) of 2105.05015; siblings 350662/350664 handled by r181/r79',
   receipts=rc('2105.05015-abs.html'),
   disposition='Basso-Dixon determinant formula for fishnet graphical functions: analytic Feynman-integral identity; no simple finite checker.'),
 '350693': dict(outcome='EXCLUDED_SOURCE_REFUTED', review_depth='2105.06777 abstract, Proposition 9, Theorem 10, Conjecture 12 read (single version)',
   receipts=rc('2105.06777-abs.html', '2105.06777.pdf', 'zbmath-tag2022.json', 'openalex-tag2022.json'),
   disposition='The source itself disproves the Coronicova Hurajova-Gago-Madaras blow-up conjecture: Hartman-Pokorna Theorem 10 (no tree of diameter >= 3, e.g. P4, has a betweenness-uniform blow-up); the abstract says "We disprove the conjecture". TAG 2022 (DOI 10.20429/tag.2022.090105): zbMATH 7510749 and OpenAlex give only the author abstract (no circulant-class content); the only full-text location is digitalcommons.georgiasouthern.edu, a denied route, so it was not requested. 337062 not touched.'),
 '350802': dict(outcome='EXCLUDED_KNOWN_RESOLUTION', review_depth='2105.12925 v2 introduction (Conder-Li D18 citation) and 2509.02778 v1 Theorem 1.3 read',
   receipts=rc('2105.12925-abs.html', '2105.12925.pdf', '2509.02778-abs.html', '2509.02778.pdf'),
   disposition='Necessity is the source corollary. Sufficiency: Kovacs-Somlai, arXiv:2509.02778 (Sept 2025) Theorem 1.3, D_2n is DCI for odd square-free n > 1; DCI implies CI; D_18 is CI by Conder-Li (cited in the source); D_4 is elementary abelian of order 4. Publicly resolved (preprint).'),
 '350816': dict(outcome='parked_deep', review_depth='arXiv abstract and versions of 2105.13357 (AAM 2022); siblings 350817/350818 HOLD in r44',
   receipts=rc('2105.13357-abs.html'),
   disposition='Classification of DAGs with toric vanishing ideals needs Groebner/elimination computations (no CAS in this lane); the r44 sibling caveats on safe gluing apply. Not attempted.'),
 '350862': dict(outcome='parked_no_finite_route', review_depth='arXiv abstract and versions of 2106.00656; sibling 350861 numerically screened by r121',
   receipts=rc('2106.00656-abs.html'),
   disposition='Coefficientwise Hankel total positivity jointly in five variables; a refutation needs a minor with a negative coefficient, which requires multivariate symbolic determinants (no CAS available). r121 found no negative numerical specialization for the sibling.'),
 '350880': dict(outcome='parked_after_exhaustive_search', review_depth='2106.01833 v1 statement (v2 withdrawn Dec 2024; the conjecture is Kamatchi-Arumugam 2013 and is not withdrawn by that); Llado-Miller partial result read (abstract, Theorem 5)',
   receipts=rc('2106.01833-abs.html', '2106.01833.pdf', 'llado-miller-upcommons.pdf', '1312.7405-abs.html'),
   disposition='Necessity is immediate. Sufficiency is open; Llado-Miller prove the case n = 2k (k leaves). Exhaustive check: every free tree of order <= 17 (counts match A000055) with no vertex adjacent to two leaves, 6,878 trees, has a verified distance-antimagic labelling (seeded local search; backtracking never needed). No counterexample.',
   search_coverage='all eligible trees n <= 17 (logs/da-trees-*.log)'),
 '350919': dict(outcome='parked_famous', review_depth='arXiv abstract of 2106.03647 (survey)', receipts=rc('2106.03647-abs.html'),
   disposition='Stanley tree-isomorphism conjecture for chromatic symmetric functions; famous; verified computationally far beyond lane capacity in the literature. Disposed quickly per brief.'),
 '350924': dict(outcome='parked_deep', review_depth='arXiv abstract of 2106.03782; sibling 350925 parked by r204', receipts=rc('2106.03782-abs.html'),
   disposition='Elementary equivalence of graph products from isomorphic cores: deep model theory; no finite route.'),
 '350926': dict(outcome='parked_deep', review_depth='arXiv abstract of 2106.03782; sibling 350925 parked by r204', receipts=rc('2106.03782-abs.html'),
   disposition='Elementary classification by cores: deep model theory (Sela, Kharlampovich-Miasnikov); no finite route.'),
}
out = {}
for i, e in E.items():
    x = ex[i]
    out[i] = {'mathdb_id': int(i), 'title': x['title'], 'source_url': x['source_url'], 'provenance': x['provenance'],
              'raw_line_file': f'raw/{i}.jsonl', 'outcome': e['outcome'], 'review_depth': e['review_depth'],
              'disposition': e['disposition'], 'search_coverage': e.get('search_coverage'),
              'lean': e.get('lean', NO_LEAN), 'credit_risk': e.get('risk'), 'source_receipts': e['receipts'],
              'history_screen': 'outputs/history-screen.json (scoped ID/arXiv search of campaign notes; numeric false positives retained)',
              'registry_screen': 'outputs/registry-screen.json (Lean Pool 01db1d70 full tree, Omega 3528d27d D5+Problems complete, OpenAI/math 4eaee875 cached listing; path screens only)',
              'proposed_for_acceptance': i == '350432', 'discovery_credit_claimed': 0}
assert len(out) == 20 and set(out) == {str(k) for k in json.loads((D / 'reservation.json').read_text())['ids']}
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
hashes = {str(p.relative_to(D)): sha(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name != 'artifact-hashes.json'}
(D / 'artifact-hashes.json').write_text(json.dumps(hashes, indent=1) + '\n')
print('results', len(out), 'hashed files', len(hashes))
