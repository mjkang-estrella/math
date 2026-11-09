import json,hashlib,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'outputs/extracted.json').read_text())
res=json.loads((L/'reservation.json').read_text())
http=[json.loads(l) for l in (L/'outputs/http.jsonl').read_text().splitlines() if l.strip()]
def rec(urlpart): return [h for h in http if urlpart in h['url'] and 'sha256' in h]
D={}
def put(i,outcome,depth,summary,**kw):
    D[i]=dict(outcome=outcome,review_depth=depth,summary=summary,**kw)
put(323488,'PARKED_FINITE_INSTANCE_VERIFIED','primary body read (arXiv:1205.1824v3: Conjectures 1 and 5, Proposition 4, Claim 6, Theorems 2-3, Propositions 16-17); exhaustive computation',
 'MathDB states Conjecture 5 (poset form). Source proves w<=3. Computed f(2,4)=8 exactly: no 9-element 2-crossing-free antichain exists in Z^4. Reduction: gap-closing in a coordinate keeps the antichain and non-crossing properties, and Proposition 17 caps each coordinate at k^(w-1)=8 distinct values, so WLOG every coordinate lies in [0,q_i-1] with max q_i=R+1<=8 attained on coordinate 1. Coverage: exhaustive max-clique over {0..4}^4 (no forcing), plus layered transversal search for R=1..7 (coordinate 1 takes all values 0..R). Via the source\'s Proposition 4 this confirms the upper bound of Conjecture 5 at k=3, w=4 (matching the source lower-bound construction). No counterexample; a parameter-instance verification only (zero credit).',
 mechanism_next='f(3,4)>=28 or f(2,5)>=17 heuristic search; exhaustive search infeasible in pure Python (box 27^4 / 16^5).',
 evidence=['outputs/323488-search-logs.txt','work/323488/clique.py','work/323488/layered.py'],
 prior_art='web search 2026-11-04: no resolution found; source 2014 JCTA version states open for w>=4. Bounded search only.')
put(324844,'PARKED','primary section read (arXiv:1301.3984v4 Section 15.7: Conjecture 15.6, Questions 15.7-15.9 and note)',
 'Color-count formulas verified by the authors through n=12 and by others through n=15; m1(n) proved by Seymour (note after Question 15.8). m2-m4 need enumeration of Hamiltonian sphere triangulations with >=17 vertices, which is infeasible in pure Python; no tractable proof mechanism.',
 prior_art='m1 case: Seymour (cited as [20] in source).')
put(326366,'EXCLUDED_SOURCE_PROVED','abstract and introduction read (arXiv:1309.5379v2, Lai)',
 'The source paper is titled and abstracted as a proof of this exact Bauer-Fan-Veldman conjecture (Conjecture 3 = [2, Conjecture 27]); MathDB itself records that the source proves it.')
put(326670,'EXCLUDED_SOURCE_REFUTED','abstract and Section 1 read (arXiv:1311.1987v1, Zhang-Zhang)',
 'Source disproves Ilic-Ilic Conjecture 1.3 explicitly (graphs G1, G2 after Conjecture 1.3; abstract "used to disprove their conjecture"); MathDB notes the refutation.')
put(327096,'EXCLUDED_KNOWN_REFUTATION','source read (arXiv:1401.5037v1 Conjecture 1); follow-up arXiv:1507.02874 introduction read',
 'Mukherjee-Kashyap-Sankarasubramaniam (arXiv:1507.02874, IEEE Trans. IT 62(7) 2016) report that a counterexample by Chan et al. shows the singleton-partition condition is not necessary for m>=4 terminals (also observed independently by Zhang et al.); m=3 proved in the source. The iff conjecture is therefore refuted in the literature.',
 receipts=rec('1507.02874'))
put(331057,'EXCLUDED_KNOWN_REFUTATION','source read (arXiv:1508.01129v1 Conjecture 1.4); arXiv:2207.03941 abstract read',
 'Local Irregularity Conjecture: the 10-vertex bow-tie graph B is decomposable but needs 4 locally irregular parts (Sedlar-Skrekovski 2021, cited in arXiv:2207.03941 abstract), so the 3-decomposition conjecture as stated is false. MathDB note "this conjecture is solved" is inaccurate in direction, but the item is settled either way.',
 receipts=rec('2207.03941'))
put(335091,'PARKED_ANALYTIC','source located (arXiv:1701.05165v2 Conjecture 1.5); statement screen',
 'Extremal Monge-Ampere eigenvalue problem over convex bodies: analytic PDE question, outside finite/kernel-checkable scope; no tractable mechanism.')
put(336555,'PARKED_CONTINUOUS','source located (arXiv:1707.01533v1 Conjecture 4.1, t=1 case via Theorem 1.5 for r>=4)',
 'Lagrangian (continuous optimisation over weightings) extension of the Complete Intersection Theorem; t=1 essentially handled in source; general t is a continuous extremal problem with no finite certificate route identified.')
put(346692,'PARKED','primary body read (arXiv:2005.14384v2: Theorem 1.8, Conjecture 1.9, Theorem 1.10, Conjecture 6.1)',
 'Source proves r>=8 for n sufficiently large and stability for all r>=4; open cases 4<=r<=7 are motivated asymptotically (stability theorem). Literal "all positive n" quantifier means small-n failures would be endpoint corrections (zero credit); a full-scope proof needs container/stability machinery for exact large-n structure. No computation run.')
put(347383,'PARKED_DEEP','source read (arXiv:2007.13999v3 Theorem 1.2, Conjecture 1.1 and motivation)',
 'Integrality forces d+3 to be an odd square, i.e. d = 6, 22, 46, 78, ...; both sides are open existence problems at d=46/47 (real Gerzon-bound ETF in dimension 47 is a long-standing open problem). No finite route.')
put(349215,'EXCLUDED_PUBLISHED_RESOLUTION','source Conjecture 1.16 located (arXiv:2012.13868v2); resolution abstract/introduction read (arXiv:2503.21215v7)',
 'Yifeng Zhang, "Multiplicity-free Levi tops and cell classification of the Gelfand S_n-graphs", arXiv:2503.21215 (v1 2025-03-27, v7 2026-09-01) proves every molecule of Gamma^row and Gamma^col is a cell; by Marberg-Zhang this is equivalent (dimension count) to irreducibility of all cell representations. Peer-review status not verified; treated as public resolution.',
 receipts=rec('2503.21215'))
put(351416,'PARKED_FINITE_RANGE_VERIFIED','source read (arXiv:2107.11422v1 Conjectures 1-2); computation',
 'Exhaustive check over all free trees with n<=18 (A000055 counts reproduced): the sun (odd n) / balanced double sun (even n) is the unique Randic-energy maximiser among trees; runner-up is the next-less-balanced double sun; minimum gap 0.0025 at n=18. Energies via Coulson integral (validated against Jacobi eigenvalues to ~1e-8). Covers trees only; Conjecture 1 (maximiser is a tree) is verified only to n=10 in the literature. No counterexample.',
 evidence=['outputs/351416-sweep-coulson.jsonl','work/351416/randic_trees.py','work/351416/validate.py'])
put(352002,'PARKED_STRONG_LEAD','primary body read (arXiv:2109.09773v3 Section 4.1.3, Tables 4-5, Conjecture 4.5); computation; published version (Discrete Math. 346(12), 2023) not read (ScienceDirect 403 policy)',
 'Reproduced Tables 4-5 exactly and extended: a_m is linear in m for n=3 (m<=7), n=4 (m<=6), n=5 (m<=6), n=6 (m<=4), with increments k = 12, 60, 280, 1260 = n(n-1)Cat(n-1) = (n-1)binom(2n-2,n-1). Mechanism validated computationally: G(m,m,n) = affine S_n modulo m times the sum-zero translation lattice (affine generators project to s_1..s_{n-1}, s~_n), so g is FC iff it has a unique minimal-length lift and that lift is FC (321-avoiding); counting these reproduces a_m and its length profile exactly for n=3,4,5, m=2,3. Full proof would need the heap/abacus classification of long FC affine permutations (Hanusa-Jones; Biagioli-Jouhet-Nadeau) plus an exact boundary count; research-scale with very high Lean cost. Conjecture appears TRUE; no counterexample.',
 evidence=['outputs/check-tables.txt','outputs/n5.txt','outputs/n6.txt','outputs/352002-affine-check.txt','work/352002/fc.py','work/352002/affine.py'],
 prior_art='web search 2026-11-04: no proof found; author homepage lists the Discrete Math. publication without a resolution; GWU thesis record 403 (not retried).',
 mechanism_next='Prove: for FC affine w, unique-minimality in w*t_{mZ^n_0} fails exactly on families whose heaps are periodic; count per period gives n(n-1)Cat(n-1).')
put(358921,'PARKED','primary body read (arXiv:2306.15130v1: Conjecture 1.1, Theorems 1.2, 1.3, 3.8, 5.1); computation',
 'Sellers proves four of the five congruences (16n+12 and 32n+24 via Theorem 1.2, 24n+20 via Theorem 3.8 alpha=1, 48n+26 via Theorem 5.1). Remaining PD_2(25n+5) = 0 mod 4 verified for all 25n+5 <= 3000 (120 values) from the eta-quotient f4 f6^2/(f1 f3 f12); proof needs a 5-dissection q-series argument, with very high Lean cost. Prior-art search found no published proof of the 25n+5 case (bounded search).',
 evidence=['outputs/358921-run3000.txt','work/358921/pd2.py'])
put(360916,'PARKED_DEEP','source read (arXiv:2311.16665v2 abstract, Conjectures 2-3, Theorem 4)',
 'MathDB item is Bowler-Brown-Fenner Conjecture 2 (2(n+1)/5 common-card bound uniqueness, n>=44). Source proves the weaker n/2+1 bound for n large (Conjecture 3 for n>=5000), not Conjecture 2. Reconstruction-family structural problem; no finite route for all n>=44.')
put(362724,'PARKED_ASYMPTOTIC','source read (arXiv:2404.08280v1 Conjecture I.1, Corollary V.1)',
 'Asymptotic O(n^{1/floor(k/2)}) bound; source confirms the case A_1=...=A_k with k a power of 2. Not finitely certifiable (asymptotic cue missed by the filter).')
put(368119,'PARKED_DEEP','source read (arXiv:2504.15693v2 Conjecture after Theorem 1.3)',
 'Exact Ramsey number R(B_n,C_m)=2n+3 for n>=3493, n>=2m+499: large-parameter Ramsey statement; source Theorem 1.3 covers larger n. No finite certificate route.')
put(373687,'PARKED_FLAGSHIP','source abstract/introduction read (arXiv:2603.17645v2)',
 'Leveque-Maffray-Trotignon 4-colour conjecture for ISK4-free graphs; best known bound 8; source treats {diamond,bowtie}-free subclass. Deep structural; disposition only.')
put(376131,'PARKED_DEEP','primary body read (arXiv:2607.17547v1 Conjecture 3, Theorem 6, Sections 2-3)',
 'Source proves n=28 and 32<=n<=10000 (computer-found transversals avoiding each entry) and shows its squares never have disjoint transversals for all n; open: n=30 (no construction even for pairwise-intersecting transversals) and a general argument for n>10000. A single n=30 square would be a parameter instance; the full-scope route needs an explicit transversal family for all n (Latin-square credited-family caution). No finite certificate resolves the conjecture.')
put(382404,'PARKED_SEARCH_NEGATIVE','primary body read (arXiv:2507.18776v2: Definition 2.2, Proposition 2.3, Lemmas 3.1-3.7, Theorem 5.2, Corollary 5.4, Conjecture 5.5, Section 7); computation',
 'MathDB defines K3-irregular as "not all distinct" (inverted; literal statement trivially false, e.g. K9 -- a paraphrase defect with zero credit); worked from the source definition (all K3-degrees distinct, Conjecture 5.5). Simulated annealing over 8-regular graphs on n=17..22 vertices (2-switch moves, incremental triangle counts; objectives: equal-pair count, plus near-collision penalty, plus target-matching) reached at best 2 equal pairs (n=20), matching the authors\' evolutionary search; in all runs triangle degrees stayed within [1,19]. No example found; nonexistence proof not attempted beyond source bounds. Coverage is heuristic only (about 1.3e8 proposed moves total).',
 evidence=['outputs/382404-run-summaries.jsonl','outputs/382404-runs-full.jsonl','work/382404/sa.py','work/382404/sa_target.py'],
 prior_art='web search 2026-11-04: no resolution; the 2026 Kyiv conference abstract (Hak-Kozerenko-Lohvynov-Yarosh) concerns K3-regular graphs (arXiv:2602.23517), a different property.',
 receipts=rec('HakKozLohYar'))
out={}
for i in res['ids']:
    e=ex[str(i)]; r=e['row']
    st=r['statement'].encode()
    d=D[i]
    out[str(i)]=dict(mathdb_id=i,title=r['title'],source_url=r['source_url'],first_stated_year=r['first_stated_year'],
        provenance=dict(chunk=e['chunk'],line_1based=e['line_1based'],chunk_sha256=e['chunk_sha256'],raw_line_sha256=e['raw_sha256'],
                        statement_sha256=hashlib.sha256(st).hexdigest(),raw_line_file=f'sources/{i}.raw.jsonl'),
        source_receipts=rec(r['source_url'].split('/')[-1]),
        historical_check='no prior mention of this ID in campaign results/ledger files (grep of results.json, SUMMARY.md, ledger.json, status.json under frontier/campaigns, 2026-11-04)',
        accepted_credit=False, **d)
assert len(out)==20
(L/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False))
from collections import Counter
print(Counter(v['outcome'] for v in out.values()))
