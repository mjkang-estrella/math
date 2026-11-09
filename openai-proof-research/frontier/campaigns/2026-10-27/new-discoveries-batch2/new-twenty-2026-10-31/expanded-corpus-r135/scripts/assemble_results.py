import json, pathlib, hashlib
D = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((D / 'extracted.json').read_text())
res_ids = json.loads((D / 'reservation.json').read_text())['ids']
receipts = {r['id']: r for r in json.loads((D / 'sources/receipts-abs.json').read_text())}
pdfrec = {r['url']: r for r in json.loads((D / 'sources/receipts-pdfs.json').read_text())}

def src(i):
    a = ex[str(i)]['source_url'].split('/')[-1]
    r = receipts.get(str(i)) or next((v for v in receipts.values() if v['url'].endswith(a)), {})
    p = pdfrec.get('https://arxiv.org/pdf/' + a, {})
    return {'arxiv': a, 'title': r.get('title'), 'authors': r.get('authors'), 'versions_seen': r.get('versions'),
            'abs_sha256': r.get('sha256'), 'pdf_sha256': p.get('sha256'), 'pdf_utc': p.get('utc'),
            'local_text': f'sources/{i}.txt'}

D_ = {
 '347138': dict(outcome='CANDIDATE_REFUTATION (ordinary proof complete; Lean draft UNCOMPILED; not self-accepted)',
   review_depth='full primary-body read of the conjecture, definitions, Theorem 19, Lemma 21 and Section 8 (arXiv v1 and published Graphs Combin. 38 (2022) 187 HTML); exhaustive and structured computation; independent finite certificate',
   summary='Conjecture 35 (Bang-Jensen, Bessy, Yeo) is false. For every m >= 3, D_m = complete digraph on A (|A| = m) plus the source W1 on B = {p1,p2,p3,p4}, with entries a1p1, a2p3 and exits p3a1, p3am, has lambda = 2 and alpha = 2, and no non-separating out-branching rooted at any vertex of A. Proof: exactly one entry lies in the branching; crossing arguments reduce to two finite W1 cases (case e = p1 is the source Theorem 19(b)).',
   mechanism='co-bipartite gluing with a 2-arc cut forces the branching to use exactly one entry; restriction to W1 gives a finite contradiction',
   checks=['logs/gadget-b4.log','logs/gadget-check.log','logs/gadget-certificate.log','logs/goodpair-check.log','logs/gadget-weak2.log','logs/gadget5-all.log','logs/gadget5-all-min1.log','logs/gadget-iso.log'],
   risks=['gadget is the source W1 (Theorem 19(b)); root to judge routine-bridge risk','refutes the rooted Conjecture 35 only; Conjecture 34 untouched (D_m has non-separating branchings from B roots)','in the two-block design W1 is the only gadget for b <= 5'],
   prior_art='published version keeps the conjecture verbatim; no refutation found by web search (2026-11-03); cited arXiv:2003.02107 has W (single, alpha 2) and alpha 3 and alpha 7 families only; D_m has all prescribed good pairs, so the mechanism differs; registry path screens clean',
   lean='candidates/347138/lean/NonSepBranching.lean (UNCOMPILED, sorry obligations listed); candidates/347138/statement-correspondence.md',
   lean_cost='moderate: finite W1 lemmas by kernel decide plus general-m crossing and connectivity lemmas'),
 '347274': dict(outcome='PARKED (investigated; no full-scope proof)',
   review_depth='full read of arXiv v1 and published Discrete Math. 344 (2021) 112389 (conjecture retained verbatim, Section 5 non-proper only)',
   summary='Conjecture 3.1: a proper perfect Mondrian partition of a square exists iff k >= 7. The only-if direction is the source own Lemma 2.1 and Propositions 2.1 and 2.2. Open part: existence of a PROPER perfect partition for every k >= 7 (source has k = 7, 8 only; Theorem 5.1 is non-proper; spiral procedure conjectural).',
   remaining_lemma='a uniform proper (simple) layout family with an equal-area square realization and provable pairwise distinct long sides for all k >= 7; equal-area realizations are irrational (rational ones would answer the integer Mondrian problem), so an all-k analytic existence plus inequality argument is needed; Lean cost high',
   attempts='spiral explorer scripts/spiral.py (diagnostic; closure variant differs from the source k = 7 layout; run log logs/spiral-5-30.log stopped at a degenerate k = 8 scan point); literature search found no later resolution (arXiv:2311.02385 concerns integer sides)'),
 '329890': dict(outcome='PARKED (open; partially known)',
   review_depth='read Section 5 of the source (Conjecture 5.7 and its exceptions)',
   summary='Harvey-Wood Conjecture 5.7 (average degree t+c-2 forces a 2-regular minor H). Csoka-Lo-Norin-Wu-Yepremyan (JCTB 2017, arXiv:1509.01185) determine the extremal function when all components are odd and bound unions of cycles; the asymptotic version is determined in arXiv:1903.03908; the kC4 case is handled by Wang and by Vicenzo-Norin. The mixed-parity finite statement is open.',
   attempts='analysed the split constructions K_s join nF0 (clique, matching, K_p blow-ups): the only violations are the excluded C_t and kC4 cases; small dense graphs are trivially fine; no counterexample route'),
 '338234': dict(outcome='PARKED (deep structural; open)', review_depth='source abstract and statement; literature search',
   summary='Kante-Kwon conjecture (vertex-minors of forests at large linear rank-width). Known for paths, stars and bounded-prime classes (arXiv:2008.00561 and others); pivot-minor analogue false for non-caterpillars. No finite certificate route.'),
 '340023': dict(outcome='PARKED (open; nearest progress is the odd-girth analogue)', review_depth='read source Conjectures 1, 4, 6, 7',
   summary='Mohar-Wu Conjecture 4 (fractional chromatic number, girth >= g). arXiv:2608.02522 (v2 Sep 2026) proves the odd-girth version, including for fractional chromatic number, and states it proves a conjecture of Mohar and Wu (Conjecture 7, odd girth). Girth >= g (even cycles) remains open. Asymptotic existence; no finite certificate.'),
 '340024': dict(outcome='PARKED (deep; open)', review_depth='read source Conjectures 5 and 6',
   summary='Mohar-Wu Conjecture 6 (weakening of Erdos-Hajnal and Thomassen). Thomassen open beyond girth 6; arXiv:2606.17901 settles Erdos-Hajnal only in polynomial-density regimes. No finite route.'),
 '341359': dict(outcome='EXCLUDED: KNOWN (published full-scope resolution)', review_depth='abstract of resolving paper',
   summary='Dross-Havet eventual sharpness conjecture confirmed by Benford and Montgomery, "Trees with few leaves in tournaments", arXiv:2103.06229 (v3 2022; JCTB 2022): for each k there is n_0 such that every (n+k-2)-vertex tournament contains every n-vertex oriented tree with at most k leaves when n >= n_0.'),
 '341385': dict(outcome='PARKED (famous open: Chen-Chvatal conjecture)', review_depth='source statement; known status',
   summary='Graph De Bruijn-Erdos (Chen-Chvatal) conjecture; long-standing open problem with extensive partial results. Small-graph verification is classical, so a brute-force sweep in pure Python would add nothing.'),
 '342566': dict(outcome='PARKED (famous open: Kelly l-reconstruction)', review_depth='source statement',
   summary='Kelly conjecture with l = 1 contains the Reconstruction Conjecture (M_1 = 3). Essentially the same conjecture as 346147.'),
 '346147': dict(outcome='PARKED (famous open: Kelly l-reconstruction)', review_depth='source statement',
   summary='Same as 342566 (Kostochka-West source); contains the Ulam reconstruction conjecture.'),
 '343364': dict(outcome='EXCLUDED: KNOWN (published proof)', review_depth='abstract of resolving paper',
   summary='Proved by Bonamy, Defrain, Hatzel and Thiebaut, "Avoidable paths in graphs", Electron. J. Combin. 27(4) (2020) P4.46, arXiv:1908.03788.'),
 '343498': dict(outcome='EXCLUDED: KNOWN (record itself and source say solved)', review_depth='source introduction read',
   summary='Wu-Zhang-Li conjecture confirmed by Esperet, Lemoine and Maffray (Discrete Math. 338 (2015)) with va_eq*(G) <= 4 for planar G (source lines 77-78).'),
 '344219': dict(outcome='PARKED (famous open)', review_depth='source statement',
   summary='Linear list-Hadwiger conjecture; best bounds are O(t log log t) (Norin-Postle-Song, Delcourt-Postle). No finite route.'),
 '344401': dict(outcome='PARKED (contains the famous majority 3-colouring conjecture)', review_depth='source Conjecture 1 and 2 and the results section',
   summary='k = 2 is the Kreutzer-Oum-Seymour-van der Zypen-Wood majority 3-colouring conjecture, which is open. Choosability is known under Delta+ <= 4, Delta <= 7, 6-choosable underlying graphs and others (source Theorems 3 and 4), so small counterexamples to the list clause would need non-6-choosable underlying graphs; not pursued.'),
 '346570': dict(outcome='PARKED (open; asymptotic)', review_depth='source statement and literature search',
   summary='DeVos-Langhede-Mohar-Samal: exponentially many f-avoiding flows for |Gamma| in {6, 7}; only Z6 has a sub-exponential bound; no later resolution found. Existence of c > 1 over all graphs; no finite certificate.'),
 '348099': dict(outcome='EXCLUDED: KNOWN (published resolution)', review_depth='source Conjecture 1.6 read; resolving abstract read',
   summary='Aougab-Clay-Rieck Conjecture 1.6 (for any r >= 3 there exists C > 0) is proved by Aougab, Clay and Hamed, "Subgraph Entropy", arXiv:2506.18838 (v3 3 June 2026): lambda > 0 depending only on r. The uniform-in-r strengthening is a different, later conjecture.'),
 '354329': dict(outcome='EXCLUDED: KNOWN', review_depth='source abstract',
   summary='Erdos high-girth Steiner triple system conjecture proved by Kwan, Sah, Sawhney and Simkin (source states this, lines 14 and 77).'),
 '355847': dict(outcome='PARKED (open; computation infeasible in lane)', review_depth='source Section 1.3 read (v2 Jan 2025)',
   summary='Felsner-Scheucher Conjecture 2.10, p3 >= n-1 for intersecting pseudocircle arrangements; exhaustively verified for n <= 7 by the authors. Extending to n = 8 needs a dedicated enumerator (not available under pure-Python caps).'),
 '381276': dict(outcome='PARKED (geometric stability; analytic)', review_depth='source statement; literature search',
   summary='Bezdek-Khan stability of the Harborth contact bound for radii in [1-eps, 1]; all-n statement with an analytic eps; no finite certificate; no resolution found.'),
 '382235': dict(outcome='PARKED (algorithmic complexity conjecture)', review_depth='source statement',
   summary='Polynomial-time Hamiltonicity for semicomplete digraphs plus k vertices; open already for k = 2 per source; not a finite certificate target.'),
}
assert set(map(int, D_)) == set(res_ids) and len(D_) == 20
out = {}
for i in res_ids:
    e = ex[str(i)]
    out[str(i)] = {'mathdb_id': i, 'title': e['title'], 'source_url': e['source_url'], 'provenance': e['provenance'],
                   'source_receipt': src(i), 'disposition': D_[str(i)]}
(D / 'results.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
print(len(out), hashlib.sha256((D / 'results.json').read_bytes()).hexdigest())
