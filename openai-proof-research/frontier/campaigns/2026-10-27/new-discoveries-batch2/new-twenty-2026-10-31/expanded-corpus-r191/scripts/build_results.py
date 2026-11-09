import json, pathlib, hashlib
L = pathlib.Path(__file__).resolve().parents[1]
ext = json.loads((L / 'extracted.json').read_text())
rec = {}
for r in json.loads((L / 'outputs/fetch-receipts.json').read_text()):
    rec[r['id']] = {k: r.get(k) for k in ('url', 'status', 'sha256', 'bytes', 'file', 'utc', 'error') if r.get(k) is not None}
def R(*ids): return [rec[i] for i in ids]
def out(name):
    p = L / 'outputs' / name
    return dict(file='outputs/' + name, sha256=hashlib.sha256(p.read_bytes()).hexdigest())

D = {}
D['327019'] = dict(review_depth='source abstract and theorem statement read (Miska, arXiv:1401.1717 v1, the MathDB source); independent numerical diagnostic',
  outcome='SOURCE-REFUTED (zero credit)',
  disposition='The MathDB record is Conjecture 2 of the source note. The same note (its abstract and main theorem) proves that v_37(a_n) <= 1 whenever 37 does not divide n, while 37 is a Schenker prime; so there is no solution modulo 37^2 and the literal statement is false by the source itself. The p = 5 case (Conjecture 1) is the source\'s proved theorem. Any refutation would be a restatement of the source.',
  computations=['scripts/schenker.py 37 2800: 37 | a_25 (Schenker witness), 76 witnesses n <= 2800 with 37 not dividing n, max v_37 = 1 (computed mod 37^3); sanity run p = 5, N = 300 gives valuations up to 3 (n = 12), as Miska proves'],
  receipts=R('arxiv-1401.1717-abs'), credit_risk='certain zero: source-refuted')
D['327069'] = dict(review_depth='Section 5 of the source (Dorais-Hirst-Shafer, arXiv:1401.3823 v2) read',
  outcome='PARKED (source-partially-resolved logic problem; outside lane)',
  disposition='Gasarch-Hirst Conjecture 4 is the source\'s Conjecture 5.4. Schmerl proved it for each fixed standard l, k (Theorem 5.5), and the source proves the full statement over RCA0 + I Sigma^0_2 (Corollary 5.11). Over plain RCA0 (non-standard l, k) it stays open; the source raises it again as Question 5.12. This is a reverse-mathematics independence question with no finite certificate and no feasible Lean route.',
  receipts=R('arxiv-1401.3823-abs', 'arxiv-1401.3823v2'), credit_risk='not attempted')
D['327142'] = dict(review_depth='abstracts of the source (Doostabadi-Farrokhi, arXiv:1401.6760) and follow-ups (Cameron-Jafari arXiv:1910.06721, Porghobadi-Jafari arXiv:1901.07184, Barbieri-Rekvenyi arXiv:2411.05429) read; survey (Kumar et al. 2021) lists it as open',
  outcome='PARKED (open; infinite-family question)',
  disposition='Known bounds: nilpotent groups at most 4, symmetric groups at most 26, alternating groups at most 22 (11 for n >= 51). No resolution found. A refutation needs an infinite family of groups with unbounded diameter, in the spirit of Giudici-Parker for commuting graphs. No finite certificate exists, and Lean cost would be very high. No concrete mechanism found in this pass.',
  receipts=R('arxiv-1401.6760-abs', 'arxiv-1910.06721-abs', 'arxiv-1901.07184-abs', 'arxiv-2411.05429-abs'), credit_risk='not attempted')
D['327206'] = dict(review_depth='source abstract (Kang-Nikiforov-Yuan, arXiv:1402.0442 v2) read',
  outcome='PARKED (analytic spectral extremal problem; deep)',
  disposition='The p-spectral radius conjecture for k-chromatic r-graphs with n > (r-1)k is analytic and has no finite certificate. Disposed quickly as the brief instructs.',
  receipts=R('arxiv-1402.0442-abs'), credit_risk='not attempted')
D['327299'] = dict(review_depth='full source TeX read (Gent-Kitaev-Konovalov-Linton-Nightingale, JIS 18 (2015) 15.6.5 = arXiv:1402.3582): definitions, Theorem on S-crucial length 17, Table 01n1n, Section 6 conjectures',
  outcome='PARKED (open; needs an infinite construction)',
  disposition='S-crucial means {0,1,n-1,n}-crucial for squares. The source finds S-crucial permutations at n = 17 (1568 of them) and n = 21 (at least 144,586 up to symmetry), and none at n = 18, 19, 20, 22. Arbitrarily long existence needs an explicit infinite family, with square-freeness of the whole family proved. No later resolution found. No finite certificate can settle it, and a construction-plus-proof would be Lean-heavy. Parked without investment.',
  receipts=R('jis-kitaev10', 'arxiv-1402.3582-abs'), credit_risk='not attempted')
D['327364'] = dict(review_depth='source v8 (arXiv:1402.6178, 2026-04-13) Section 19 read',
  outcome='PARKED (open in the current source version; research-level; rowmotion family)',
  disposition='This is the source\'s Conjecture 19.5. The current v8 still lists it as open for even p: Propositions 19.6 and 19.7 prove only odd p, Remark 19.3 identifies NEtri(p) for even p with the type-B root poset, and the authors verified it by Sage for small p. A proof for all even p would be significant but has no finite certificate, and the brief notes the nearby 346742 rowmotion family. Johnson-Liu (arXiv:2311.07133) handle trapezoids, not this poset. No tractable mechanism found in this pass.',
  receipts=R('arxiv-1402.6178-abs', 'arxiv-1402.6178v8'), credit_risk='not attempted')
D['327443'] = dict(review_depth='source abstract (Adiprasito PhD thesis, arXiv:1403.2657) plus literature search',
  outcome='KNOWN (disproved; zero credit)',
  disposition='Shephard\'s combinatorial subpolytope conjecture was disproved by Adiprasito-Padrol (A universality theorem for projectively unique polytopes and a conjecture of Shephard, Israel J. Math. 2016, arXiv:1301.2960): a 5-dimensional counterexample, and that work is part of the source thesis itself. Only the d = 4 case is still open (Padrol HDR), and the MathDB statement says "for every d".',
  receipts=R('arxiv-1403.2657-abs'), credit_risk='certain zero: published disproof')
D['330334'] = dict(review_depth='source v4 (arXiv:1504.06257, Adv. Appl. Math. 2017) Conjectures 2.12-2.14 read; citing-work search found no resolution',
  outcome='PARKED (deep classification conjecture)',
  disposition='This is Conjecture 2.13, retained in v4. Known cases: gamma <= 1, gamma <= 2 (Alfaro-Valencia) and gamma <= 3. A finite classification for every k is a structural statement with no finite certificate. Not attempted.',
  receipts=R('arxiv-1504.06257-abs', 'arxiv-1504.06257v4'), credit_risk='not attempted')
D['330335'] = dict(review_depth='as 330334 (Conjecture 2.14 of the same source, retained in v4)',
  outcome='PARKED (deep; same family as 330334)',
  disposition='The weak form of 330334 for nested infinite families. It needs a structure theorem; there is no finite certificate.',
  receipts=R('arxiv-1504.06257-abs', 'arxiv-1504.06257v4'), credit_risk='not attempted')
D['330501'] = dict(review_depth='source abstract (Hunt-Keese-Licata-Morrison, arXiv:1505.04484) read',
  outcome='PARKED (deep low-dimensional topology; outside lane)',
  disposition='A collapse conjecture for the sutured-annular-to-Khovanov spectral sequence. Deep, with no finite discrete certificate; disposed quickly per the brief.',
  receipts=R('arxiv-1505.04484-abs'), credit_risk='not attempted')
D['330528'] = dict(review_depth='source abstract (Kalai survey, arXiv:1505.04952) read',
  outcome='PARKED (asymptotic extremal; famous family)',
  disposition='The Frankl-Rodl theorem with sum restrictions is an exponential-asymptotic statement with no finite certificate. Disposed quickly per the brief.',
  receipts=R('arxiv-1505.04952-abs'), credit_risk='not attempted')
D['330821'] = dict(review_depth='original BJGL paper (J. Graph Theory 22 (1996), RHUL copy) Sections 5-6 read; MathDB source (R. Wang, arXiv:1506.07949 v3, DMTCS 2017) abstract; Wang-Wu AJC 77 (2020) status paragraph; arXiv:2504.21628 (Graphs Combin. 2026) introduction',
  outcome='PARKED after sustained bounded search (no counterexample; open)',
  disposition='This is BJGL Conjecture 6.1 (= Wang-Wu Conjecture 1.3). As of AJC 2020 it is "still open and seems quite difficult"; the stronger Conjecture 1.4 (dominated pairs only) was disproved by Wang-Chang-Wu (Discrete Math. 343 (2020) 111794). The Bang-Jensen-Guo-Yeo 5n/2 - 4 theorem settles n <= 6, so a counterexample needs n >= 7 and, at n = 7, a constrained pair of degree sum exactly 13. A simulated-annealing search (objective: total degree-sum deficit over non-adjacent dominating or dominated pairs, restricted to strong non-Hamiltonian digraphs; random and non-1-tough seeds; exact subset-DP Hamiltonicity test) at n = 6, 7, 8, 9, 10 never got below deficit 1, the level of the printed 2n - 2 sharpness example. Calibration: the same code finds counterexamples to the disproved Conjecture 1.4 within seconds (966 labelled examples at n = 6 in 60 s; 5 at n = 8 in 30 s). One was confirmed by an independent permutation brute-force checker (scripts/bjgl_verify.py): strong, non-Hamiltonian, minimum dominated-pair sum 11 = 2n - 1, minimum dominating-pair sum 7. This is bounded heuristic evidence only, not an exhaustive coverage claim.',
  computations=['scripts/bjgl_sa.py runs: ' + ', '.join(f'outputs/{n}' for n in [
      'bjgl-sa-n6-s1.json', 'bjgl-sa-n7-s11.json', 'bjgl-sa-n7-s41-mix.json', 'bjgl-sa-n8-s21.json', 'bjgl-sa-n8-s51-tough.json',
      'bjgl-sa-n9-s31.json', 'bjgl-sa-n10-s61-mix.json', 'bjgl-sa-dominated-n6-s5.json', 'bjgl-sa-dominated-n8-s71.json']),
      'Coverage: about 7.6M annealing steps at n = 7 (two runs, 90 s each), 4.8M at n = 8, 1.36M at n = 9, 0.33M at n = 10; best deficit 1 throughout.'],
  receipts=R('bjgl-sufdi3', 'arxiv-1506.07949-abs', 'ajc-v77-p136', 'arxiv-2504.21628-abs', 'arxiv-2504.21628'),
  credit_risk='no candidate. A counterexample would be a finite, Lean-friendly certificate, but none was found; the conjecture has resisted experts since 1996.')
D['330961'] = dict(review_depth='full source (Cranston-Rabern, arXiv:1507.05600) Sections 2, 4 and 5 read; independent fixability solver written and validated',
  outcome='PARKED after bounded exhaustive tests (no counterexample)',
  disposition='This is the source\'s Conjecture 4.1. I wrote an independent bottom-up fixpoint solver for (L,P)-fixability (Definition 1), quotiented by colour permutations (state = multiset of colour-membership vectors), with superabundance computed over connected edge subsets. Validation: it reproduces Figure 8(a) (C5 superabundant, non-fixable) and Theorem 2.5 (stars: 689 superabundant assignments all fixable, heights up to 3); the Lemma 2.2 counter (fixable but not superabundant) is 0 everywhere. Every exhaustively tested profile within the hypothesis of 4.1 is fixable: P5 with seven profiles at k = 7, P6 with five profiles at k = 6 (up to 41,280 states, heights up to 12), and the 7-vertex spider S(2,2,2) with two profiles at k = 6 (up to 53,616 states). Non-fixable superabundant states appear only outside the hypothesis (for example P5 with all internal vertices at degree). Bounded evidence; pots are limited to k colours.',
  computations=['outputs/fix-sweep-p5-k7.json', 'outputs/fix-sweep-p6-k6.json', 'outputs/fix-sweep-spider222-k6.json', 'outputs/fix-star4-l2-k7.json'],
  receipts=R('arxiv-1507.05600-abs', 'arxiv-1507.05600'), credit_risk='no candidate')
D['330962'] = dict(review_depth='source Section 4.1 read; Figure 8(a) reproduced by the lane solver',
  outcome='SOURCE-REFUTED (zero credit)',
  disposition='This is the source\'s Conjecture 4.2, labelled "(false)" in the source itself, with explicit C5 counterexamples in Figure 8. The lane solver confirms Figure 8(a) is superabundant and not fixable (closure of 23,846 canonical states, pot 8).',
  computations=['scripts/fix.py closure on the Figure 8(a) lists: superabundant = true, colourable = false, height = null (not fixable)'],
  receipts=R('arxiv-1507.05600'), credit_risk='certain zero')
D['330963'] = dict(review_depth='source Conjecture 4.3 and Lemma 4.4 read; bounded exhaustive tests with the lane solver',
  outcome='PARKED after bounded exhaustive tests (no counterexample)',
  disposition='Parts (a) and (b) are special cases of 330961, and the authors report a draft proof of (a). Exhaustive tests on the star with one edge subdivided: D = 3 with 22 list-size profile runs (11 at k = 7, 10 at k = 10, 1 minimal at k = 7); D = 4 with two saved profiles at k = 6 (up to 23,983 states), plus [4,2,1,2,2,2] at k = 6 (7,800 states, 0 bad), whose output file was overwritten by the later run; a D = 4, k = 8 run hit the 100 s cap and produced no result. Every superabundant non-fixable assignment has |L(r)| = d(r), |L(s)| = d(s) and psi_L(G) = ||G|| exactly, so none violates (a), (b) or (c) (bad_with_psi_gt_E = 0 in every profile). This is consistent with the conjecture and shows the (c) threshold is tight in the tested range.',
  computations=['outputs/fix-sweep-ss3-k7.json', 'outputs/fix-sweep-ss3-k10.json', 'outputs/fix-sweep-ss4-k6.json', 'outputs/fix-ss3-min-k7.json'],
  receipts=R('arxiv-1507.05600'), credit_risk='no candidate')
D['331147'] = dict(review_depth='source abstract (Kraner Sumenjak-Peterin-Rall-Tepeh, arXiv:1508.04029 v3, DMTCS 2016); resolving paper abstract (Commun. Comb. Optim., DOI 10.22049/cco.2026.31349.2826) read',
  outcome='KNOWN (published resolution; zero credit)',
  disposition='Hernandez Martinez and Peterin, "New characterization of efficient closed and open dominated graphs" (CCO 2026), state that they solve the Kuziak-Peterin-Yero torus EOD conjecture for C_t box C_r. Only the abstract was read, not the proof body; it is an explicit published resolution.',
  receipts=R('arxiv-1508.04029-abs', 'combopt-15176'), credit_risk='certain zero: published resolution')
D['331434'] = dict(review_depth='source abstract (Tomon, arXiv:1509.07346) read',
  outcome='PARKED (asymptotic chain-partition conjecture; famous Furedi family)',
  disposition='This asks for N(h) such that for odd n > N(h) the Boolean lattice partitions into rank-symmetric chains of size 2h, with one exception. It is asymptotic in n, with no finite refuting certificate; disposed quickly per the brief.',
  receipts=R('arxiv-1509.07346-abs'), credit_risk='not attempted')
D['331440'] = dict(review_depth='source abstract (Bergelson-Moreira, arXiv:1509.07574) read',
  outcome='PARKED (infinitary Ramsey / ergodic question)',
  disposition='Whether every DC set contains {x+y, xy} is an infinitary statement about central-set classes, with no finite certificate.',
  receipts=R('arxiv-1509.07574-abs'), credit_risk='not attempted')
D['331551'] = dict(review_depth='source abstract (Xia-Fang, arXiv:1510.02740 v4) and Xia arXiv:1709.09157 abstract read',
  outcome='SOURCE-REFUTED as printed (zero credit)',
  disposition='The literal MathDB statement ("every finite nonabelian simple group has a cubic GRR") is false by the source\'s own theorem: PSL_2(7) has no cubic GRR. The working replacement ("finitely many exceptions", Xia-Fang) is a different, deep classification statement handled by later papers (Xia 2017-2019; Xia-Zheng-Zhou 2022; Li-Zhang-Zheng 2022), near the 337175 and 357933 family. Not attempted.',
  receipts=R('arxiv-1510.02740-abs', 'arxiv-1709.09157-abs'), credit_risk='certain zero for the literal statement')
D['350219'] = dict(review_depth='source abstract (Rukavicka, arXiv:2103.14609) and claimed-resolution abstract (Rukavicka, arXiv:2410.12714 v2) read',
  outcome='KNOWN-CLAIMED (public preprint proof; zero credit)',
  disposition='Rukavicka, "Palindromic length of infinite aperiodic words" (arXiv:2410.12714, 2024) claims a proof of the 2013 Frid-Puzynina-Zamboni conjecture. The prefix form is equivalent by the cited Saarela/Frid equivalence. Even if the claim is unverified, this is a famous infinite-word conjecture with no finite certificate.',
  receipts=R('arxiv-2103.14609-abs', 'arxiv-2410.12714-abs'), credit_risk='certain zero')

assert set(D) == set(ext), set(ext) ^ set(D)
res = {}
for i in sorted(ext, key=int):
    e = ext[i]
    res[i] = dict(mathdb_id=int(i), title=e['title'], source_url=e['source_url'], provenance=e['provenance'], **D[i])
(L / 'results.json').write_text(json.dumps(res, indent=1, ensure_ascii=False) + '\n')
print(len(res), 'entries'); print({i: res[i]['outcome'] for i in res})
