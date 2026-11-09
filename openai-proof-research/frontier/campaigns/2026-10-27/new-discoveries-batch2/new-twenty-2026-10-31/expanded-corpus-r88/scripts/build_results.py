# Build results.json (exactly the 20 reserved IDs) from extracted.json, source receipts and the dispositions below.
import json, pathlib, hashlib
D=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((D/'extracted.json').read_text()); res=json.loads((D/'reservation.json').read_text())
def rec(name):
    p=D/'sources'/f'{name}.receipt.json'
    if not p.exists(): return {'name':name,'missing':True}
    r=json.loads(p.read_text()); return {'name':name,'url':r.get('url'),'utc':r.get('utc'),'status':r.get('status'),'sha256':r.get('sha256'),'bytes':r.get('bytes')}
K='KNOWN_IN_LITERATURE_EXCLUDED'; P='PARKED_OPEN_NO_CANDIDATE'
dis={
 341752:dict(outcome=K,review_depth='source abstract read (arXiv 1902.00353); prior-proof abstracts read (arXiv 2311.05762, 2404.02244); proof bodies not re-audited',
  receipts=['abs-1902.00353','abs-2311.05762','abs-2404.02244'],
  disposition='Marton/PFR over F_p^n is proved: Gowers-Green-Manners-Tao, arXiv 2311.05762 (characteristic 2) and arXiv 2404.02244 (abelian groups of bounded torsion, which contains F_p^n; covering by (2K)^{O(p^3)} translates of a subgroup of size at most |A|). Known theorem; zero credit.',
  attempt='None (known).',remaining='None.'),
 341753:dict(outcome=K,review_depth='source abstract read (arXiv 1902.00353: "we discuss a counterexample to this conjecture")',
  receipts=['abs-1902.00353'],disposition='Refuted in the source itself (Aaronson 2019). The MathDB record states the variant is refuted. Known; zero credit.',attempt='None.',remaining='None.'),
 342072:dict(outcome=P,review_depth='source abstract read; Chu arXiv 1906.03793 abstract read; Kumar-Mohan-Pandey, Integers 26 (2026) #A58 full PDF text read (Section 1 setup, Theorems 1 and 2, statement of the two unsolved cases, Lemmas 14-16)',
  receipts=['abs-1903.03533','abs-1906.03793','kumar-integers-aa58'],
  disposition='Largely resolved in literature: equal common differences by Chu (Integers 2020 A87 / arXiv 1906.03793); different differences by Kumar-Mohan-Pandey (2026) except two explicit residual overlapping cases [(i) gcd(q1,q2)>1 and 0<d2<(m1-1)d1; (ii) q1=2, gcd(2,q2)=1, 0<d2<(m1-1)d1]. Residual cases remain open per that paper.',
  attempt='Capped exhaustive searches: 1,955,629 distinct unions (both differences <=10, lengths <=20, offsets |b|<=70; logs/ap2.log) and 5,118,901 distinct unions inside the residual cases (d1<=12, d2<4*d1, lengths<=14; logs/ap3.log): no sum-dominant set (max |S+S|-|S-S| = 0).',
  remaining='Proof of the two residual cases plus a Lean formalisation of Chu and Kumar-Mohan-Pandey case analyses (full literal endpoint) - infeasible in this pass. Even a residual-case proof would be a completion of a largely solved conjecture.'),
 343949:dict(outcome=P,review_depth='source PDF text read around Conjectures 2.8-2.14 (arXiv 1909.13143); web search on Aharoni-Berger status (no full proof found; Blinovsky arXiv 1904.06747 is an unrefereed sketch)',
  receipts=['abs-1909.13143','pdf-1909.13143'],
  disposition='Source Conjecture 2.10 (every n-1 matchings of size n in a bipartite graph have a full rainbow matching): Aharoni-Berger-type generalisation of Ryser-Brualdi-Stein; famous open problem with partial results (Pokrovskiy, Munha Correia-Pokrovskiy-Sudakov asymptotics; Montgomery for Latin squares only). Not a tractable small-instance target (unbounded vertex sets).',
  attempt='Trivial for n<=3 (n=3: pick e1 in M1; at most 2 edges of M2 meet e1). No search run.',remaining='Full conjecture.'),
 343968:dict(outcome=P,review_depth='source PDF text read (arXiv 1909.13663: Sections 1, Theorem 19, Theorem 21, final Problems)',
  receipts=['abs-1909.13663','pdf-1909.13663'],
  disposition='Open. The MathDB parser label "disproved" is wrong: Csirmaz refutes only the almost-perfect analogue (Theorem 21) and states "The original problem remained unsolved"; Theorem 19 shows the ideal-duality conjecture is equivalent to duality of entropic matroids. No finite search route.',
  attempt='None beyond source reading.',remaining='Equivalent entropic-matroid duality problem.'),
 344911:dict(outcome=P,review_depth='source abstract read (arXiv 1912.07021)',receipts=['abs-1912.07021'],
  disposition='Infinite-dimensional global continuation conjecture (separable Hilbert spaces, compact N,C); authors could neither prove nor disprove. No finite route; not Lean-feasible here.',attempt='None.',remaining='Full conjecture.'),
 345244:dict(outcome=P,review_depth='source PDF text read (arXiv 2001.07925: Section 2 definitions, eq. (2.1), Definition 2.9, Examples 2.12-2.15, Section 4 to Conjecture 4.7)',
  receipts=['abs-2001.07925','pdf-2001.07925','graphdata/graph9c.g6','graphdata/g10/graph10c.g6.gz (curl; sha256 ddabd151a69913720065bcbc09fcbcddc56f57f95c66a5728338177ec26fd56a, resumed download, gzip -t ok)'],
  disposition='Strongest finite route of the pass; no counterexample. New partial lemma (ordinary proof, not Lean-checked): under (S1),(S2) the pointed graph produces a hypergroup iff the quotient matrices B_i of the distance partition commute; consequently Conjecture 4.7 holds whenever ecc(v0)<=2, and every counterexample is non-vertex-transitive with ecc(v0)>=3.',
  attempt='Exhaustive: all connected graphs <=10 vertices (McKay catalogue; every (S1)+(S2) pointed graph there is distance-regular). Layered BFS generator validated against the catalogue: complete (n,r) in {(12,3),(14,3),(16,3),(18,3) [8 shards, all complete; 80 pointed (S1)+(S2) labelled outputs, 64 non-distance-regular],(11,4),(12,4),(12,5)}; partial: (13,4) [8 shards, 2 complete], (14,4) [8 shards, none complete], (20,3),(15,4),(16,4) unsharded. Hundreds of non-distance-regular (S1)+(S2) pointed graphs found (e.g. a 12-vertex cubic graph, v0-orbit {0,10,11}); all produce hypergroups. Bi-circulants over Z_m complete for m<=15 (|S0|=|S1|<=4,|T|<=3) - all (S1)+(S2) ones distance-regular. See mathematical-attempts.md section 1.',
  remaining='Show [B_i,B_j]=0 from (S1),(S2) for ecc(v0)>=3 (for ecc 3 exactly [B_1,B_2]=0), or find a non-VT distance-degree-regular graph with ecc(v0)>=3 where it fails.'),
 346674:dict(outcome=P,review_depth='source PDF text read (arXiv 2005.13765: Conjectures 1.4, 1.8, 1.9; Theorem 1.10)',receipts=['abs-2005.13765','pdf-2005.13765'],
  disposition='Open; source proves only the special cases of Theorem 1.10. Analytic scattering problem; no finite route.',attempt='None.',remaining='Full Conjecture 1.9.'),
 350410:dict(outcome=K,review_depth='source abstract read (arXiv 2104.06959 v3; Graphs Combin. 39 (2023) 32)',receipts=['abs-2104.06959'],
  disposition='Disproved in the source itself (Haslegrave: the modified inequality conjecture is still false in general). Known; zero credit.',attempt='None.',remaining='None.'),
 351476:dict(outcome=K,review_depth='source abstract read; Altman arXiv 2210.17493 PDF text read at Conjecture 1.2 / Corollary 1.4',receipts=['abs-2107.14413','abs-2210.17493','pdf-2210.17493','abs-2404.17005'],
  disposition='Proved: Altman, "Local aspects of the Sidorenko property for linear equations", Corollary 1.4 ("Conjecture 1.2 [= KLM Conjecture 5.1] is true"), Forum Math. Sigma 13 (2025) e177. Known; zero credit.',attempt='None.',remaining='None.'),
 352298:dict(outcome=P,review_depth='source abstract read (arXiv 2110.09679); web search found no later resolution',receipts=['abs-2110.09679'],
  disposition='Open geometric conjecture on great-circle thrackle drawings of augmented caterpillars; continuous geometry, no capped exhaustive model fixed in this pass.',attempt='None.',remaining='Full conjecture (source suggests crossing orientations).'),
 352675:dict(outcome=P,review_depth='source abstract read (arXiv 2111.09345)',receipts=['abs-2111.09345'],
  disposition='Step in a programme towards a Deift-conjecture counterexample (comb domains, KdV); analytic, no finite route.',attempt='None.',remaining='Full conjecture.'),
 353070:dict(outcome=P,review_depth='source PDF text read (arXiv 2112.13321: Definition 2.7, Theorem 2.9, Conjectures 2.10, 9.6, 9.7 and the quadratic minor-lift formula); web search found no resolution',receipts=['abs-2112.13321','pdf-2112.13321'],
  disposition='Open; numerical diagnostics negative.',
  attempt='Random sampling (n=3,4,5; ~2.2M Lorentzian/matrix samples, ~316k in H(P)) and adversarial Nelder-Mead (n=3,4,5) found no violation of spectral containment (logs/sc-*.log, logs/sco-*.log).',
  remaining='Full Conjecture 9.7; a counterexample would also need an exact algebraic certificate.'),
 353123:dict(outcome=K,review_depth='source abstract read and PDF text read at Section 6 "Counterexample" (arXiv 2112.14914: counterexample to [3, Conjecture 6.1], the reserved statement)',receipts=['abs-2112.14914','pdf-2112.14914'],
  disposition='Refuted in the source itself (Brettell-Semple-Toft give a counterexample). Known; zero credit.',attempt='None.',remaining='None.'),
 353422:dict(outcome=P,review_depth='source PDF text read (arXiv 2201.11548: Theorem 1.1, Section 5, Conjecture 5.4 and the 7,7,2 example); Chen-Fiujlaali arXiv 2608.00791 abstract read (2026; treats conjecture as open, proves a range)',
  receipts=['abs-2201.11548','pdf-2201.11548','abs-2608.00791'],
  disposition='Open for odd d>=3 (even d and simple graphs follow from source Theorem 1.1; d=1 is Goldberg-Seymour). No counterexample found.',
  attempt='Exact ILP (HiGHS) search with prefilter by the proved bound ceil((3D-1)/(3d-1)): n=3 multiplicity<=16 (d=3,5), n=4 multiplicity<=7 (d=3,5), n=4 max-multiplicity shards 8,9 (d=3), n=5 multiplicity<=3 (d=3) complete; n=4 shards 10,11 and n=5 shard 4 hit the CPU cap. Zero counterexamples.',
  remaining='Full conjecture for odd d>=3 (structural analogue of Goldberg-Seymour).'),
 353625:dict(outcome=P,review_depth='source PDF text read (arXiv 2202.06785: Section 2 definitions, Theorem 2.1, Proposition 2.3, Conjecture 4.1 and the G(8,3) remark); web search: no resolution found (J. Algebraic Combin. 59 (2024))',
  receipts=['abs-2202.06785','pdf-2202.06785'],
  disposition='Open; no counterexample. Elementary lemma: in a non-core non-bipartite G(n,k) every endomorphism maps each shortest odd (rim) cycle isomorphically onto a rim cycle; prisms G(n,1) satisfy the conjecture (images are V or a rim).',
  attempt='Exact endomorphism-image enumeration for every non-core non-bipartite G(n,k), n<=40, k!=1 (complete except the G(3m,m) family and 7 capped cases); subset-based independent check for n<=11 (reproduces the bipartite G(8,3) counterexample of the source); randomised sampling to n=24. Every image found is a retract. See mathematical-attempts.md section 2.',
  remaining='Classification of images for the non-core families of Theorem 2.1(c) with explicit retractions.'),
 353943:dict(outcome=P,review_depth='source PDF text read (arXiv 2203.08305: Section 1 definitions, Propositions 8-10, Conjecture 4, Examples 15-16)',receipts=['abs-2203.08305','pdf-2203.08305'],
  disposition='Open; verified computationally for all binary matroids of rank <=6: every 3-connected orderable binary matroid of rank <=6 is graphic.',
  attempt='Exact CSP orderability (two solvers cross-checked; source examples reproduced) with exhaustive deletion-closed closure over subsets of PG(r-1,2) containing a fixed basis, pruning spanning-circuit branches by source Prop. 9: rank<=5 no candidate; rank 6: 104 coordinate-permutation classes of 3-connected orderable matroids without spanning circuit, all graphic (e.g. M(K_{3,4})).',
  remaining='Full conjecture (ranks >=7 untested).'),
 354292:dict(outcome=K,review_depth='source abstract read (arXiv 2204.07567: "We provide a counterexample to a conjecture of Frankl")',receipts=['abs-2204.07567'],
  disposition='Refuted in the source itself. Known; zero credit.',attempt='None.',remaining='None.'),
 354889:dict(outcome=P,review_depth='source PDF text read (arXiv 2206.02576 Conjecture 2.2); Hollom arXiv 2411.16844 (v5) abstract and PDF text read around Example 2.1 / Question 3.1; Hollom arXiv 2607.02500 abstract read',
  receipts=['abs-2206.02576','pdf-2206.02576','abs-2411.16844','pdf-2411.16844','abs-2607.02500'],
  disposition='Open. Hollom disproved the FAC (Aharoni-Korman) version, but his counterexample has width aleph_0; he states the finite-width question (his Question 3.1, equivalent in spirit to the MathDB bounded-width statement) remains open even for countable width 3. Infinite posets; no finite route.',
  attempt='None beyond literature.',remaining='Full bounded-width conjecture.'),
 355966:dict(outcome=K,review_depth='source abstract read (survey arXiv 2209.01201); Nambi-Kumar arXiv 2406.05960 abstract read; Jayanthan-Kumar-Sarkar arXiv 1904.04499 abstract read',
  receipts=['abs-2209.01201','abs-2406.05960','pdf-2406.05960','abs-1904.04499'],
  disposition='Resolved: Nambi-Kumar (arXiv 2406.05960) prove linear type for trees and show that not all unicyclic graphs have binomial edge ideals of linear type, so the literal "tree or unicyclic" statement is false and known. Zero credit.',attempt='None.',remaining='None.'),
}
assert sorted(dis)==sorted(res['ids']) and len(dis)==20
out={}
for i in res['ids']:
    e=ex[str(i)]; d=dis[i]
    out[str(i)]={'mathdb_id':i,'title':e['title'],'literal_statement':e['statement'],'source_url':e['source_url'],
      'provenance':e['provenance'],'history_check':'history-matches.txt: only ledger reservation lines and unrelated hash-substring collisions; keyword screen (family terms) found no prior lane work on these IDs',
      'review_depth':d['review_depth'],'outcome':d['outcome'],'disposition':d['disposition'],'mathematical_attempt':d['attempt'],
      'remaining_lemma':d['remaining'],'source_receipts':[rec(x) if not x.startswith('graphdata/g10') else {'note':x} for x in d['receipts']],
      'candidate':False,'Lean_complete':False,'novelty_clearance':False,'accepted_credit':0}
(D/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(len(out), {o:sum(1 for v in out.values() if v['outcome']==o) for o in (K,P)})
