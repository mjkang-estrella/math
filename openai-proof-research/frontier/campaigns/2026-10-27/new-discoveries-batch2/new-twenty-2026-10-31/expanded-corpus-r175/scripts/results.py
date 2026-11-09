import json,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'extracted.json').read_text())
rec=json.loads((L/'outputs/fetch-receipts.json').read_text())
def receipts(i,extra=()):
    out={}
    for r in rec:
        k=r['id']
        if k.startswith(str(i)) or k=='eprint/'+str(i) or k in extra:
            out[k]={kk:r.get(kk) for kk in ('url','status','sha256','utc','error') if r.get(kk) is not None}
    return out
D={
362785:dict(outcome='CANDIDATE_FULL_PROOF',review_depth='source TeX v2 read in full for Sec. 6 (construction, Obs. obs:neighbors, Lemmas reducetofinite, qk2-free, infinite-easybounds, lowerpath, Conjecture con:path); web search; GitHub + Lean Pool + Omega/OpenAI screen',
 summary='Full proof for all odd q>=3, p>=1 that G_{q,p} is P_{3q-2}-free (sharp by source Lemma lowerpath). Route: translation to a linear model (i<j adjacent iff j-i=1 or j-i = -1 mod q), (star) non-adjacent residue-consecutive pairs are ordered, Lemma A no independent residue transversal, Lemma B (source Claim cla:one-edge in path form), run-structure Lemma C, deficit case analysis forcing an independent transversal. Independent checks: combinatorial step for q<=11 (walkcheck), exhaustive infinite-model search q=7 (no P_19, 3261 prefixes, ~64M nodes), q=3,5 maxima reproduced.',
 computation='scripts/gqp.py, lamq.py, lamq2.py, lamq3.py, walkcheck.py; logs/gqp-*.log, lamq*.log, walkcheck.log',
 credit_claim='candidate only; credit risk moderate-high (new part ~1 page on top of source Claim cla:one-edge / clm:ordering machinery); see CANDIDATE-362785.md'),
362816:dict(outcome='PARKED_OPEN_BOUNDED_SEARCH',review_depth='source TeX read (Def. 1, Thms 2-4, 11, nearly-complete graph theorems, Sec. 4 Tables 1-4, Conjecture conj1); web search',
 summary='Conjecture drn(G)<=|V(G)| except Kbar2, Kbar3, P3. Authors verified all graphs of order <=7 by Sage (Table 4). My independent row-wise permutation embedding search reproduced 0 failures for all connected graphs and complement-disconnected graphs of order 4,5,6 and the first 326 of 853 connected order-7 graphs (100 s cap). Order 8 (12346 graphs) infeasible in pure Python within lane caps (no numpy). No counterexample; no proof route (needs a general Latin-array construction).',
 computation='scripts/drn.py; logs/drn-n4-7.log'),
362880:dict(outcome='PARKED_STRUCTURAL',review_depth='abstract; TeX conjecture location',summary='Existence of a finite forbidden-subdiagram family characterizing shellability of Kohnert posets; existential/structural, no finite certificate route. Parked.'),
363028:dict(outcome='PARKED_OPEN_BOUNDED_SEARCH',review_depth='source TeX read (rules, Prop. copycat involution, Prop. grids, Sec. 7 conjectures, computation table); web search; GitHub (authors code mackenziecarr/Trail-Trap, not Lean)',
 summary='Same-parity grids are P2-win by the source involution; open cases are mixed parity. Memoized exact solver (validated on K4, K13, K33, K35, K6, P2xP5, P2xP7 = source values) shows P2-win for 3x4, 3x6, 3x8, 4x5, 4x7; 5x6: 18 opening classes all P2-win before the cap. No counterexample; no general P2 strategy found.',
 computation='scripts/trailtrap.py, trailtrap_selftest.py; logs/trailtrap-*.log'),
363373:dict(outcome='SOURCE_DISPROVED',review_depth='abstract (Hollom arXiv:2406.01790) and MathDB record',summary='The hypergraph bunkbed conjecture is disproved in the source itself by an explicit hypergraph (Hollom 2024); MathDB record says so. Zero credit.'),
363445:dict(outcome='PARKED_HEAVY_MACHINERY',review_depth='abstract; TeX section list',summary='Converse of sparse paving characterization by Schubert coefficients (Berget-Fink Chow-class coefficients). A test needs computing Schubert coefficients of non-sparse-paving connected matroids; not implementable within lane limits. Parked.'),
363809:dict(outcome='PARKED_OPEN',review_depth='source TeX read (definitions, Prop. tangram q, Cor. lower bound, closing remarks, conjecture); web search',summary='a(k)<=k+3 for k-anagram-free words is the Alon-Grytczuk-Michalek-Lason 2009 question; only a(1)=4 known. A refutation would need a finite backtracking proof that no long word over k+3 letters avoids split number <=k (first case k=2, 5 letters); not attempted beyond analysis (likely huge tree, probably true). No resolution found in literature search.'),
363910:dict(outcome='PARKED_ANALYTIC',review_depth='abstract v3 (Jul 2026)',summary='FKM pairwise partition regularity; v3 of the source still conditional/partial (Elliott-type conjecture for some (a,b,c)); analytic number theory, no finite route.'),
363938:dict(outcome='SOURCE_CONTRADICTED_ZERO_CREDIT',review_depth='source TeX read in full (ID/rID definitions, Props, Thm C_r(G,s)=C_r(G,-s), Prop prop_relaxed-H_n, Sec. 5 conjectures)',
 summary='Printed bound C_r <= min{l, ceil(3n/5-4)} for all n>=1 is contradicted by the source itself: the bound is negative for n<=5 (C_r>=0), and the source Prop prop_relaxed-H_n.4 gives C_r(K_{t,t},tau_t)=t-2, exceeding ceil(3n/5-4) at n=6,8,10 (values 1>0, 2>1, 3>2). Source-internal correction: zero credit. The separate claim C_r<=l was not searched (any counterexample would only re-refute an already source-refuted statement).'),
363994:dict(outcome='PARKED_ANALYTIC',review_depth='abstract v2 (Adv. Math. 2026)',summary='Source proves subcube extremality for beta>=0.50057 (computer-assisted interval arithmetic); remaining 1/2<=beta<0.50057 analytic. No finite route.'),
364116:dict(outcome='PROVED_ROUTINE_ZERO_CREDIT',review_depth='source TeX read (conjecture lines 1946-1960, species identity Prim\'=Cay^2); web search; citing paper arXiv:2507.09304 checked (does not state it)',
 summary='Both equalities have a five-line proof: (i) by position symmetry #{w in Cay[n]: w_i=j} = #{w: w_1=j}, so sum_w sum_{i in fix(w)} i = sum_j j N(j) = sum_w w_1 = (1/n) sum_w sum_i w_i; (ii) by the source identity |Prim\'[n]| = sum_k C(n,k)F_k F_{n-k} = sum_w (max w + 1) and block-reversal symmetry, sum_w w_1 = (1/2) sum_w (max w+1). Verified by brute force n<=7. Routine double counting plus a source identity: zero credit expected.',
 computation='scripts/cay364116.py; logs/cay364116.log'),
364120:dict(outcome='SOURCE_RESOLVED',review_depth='source TeX read (Thm t:total-SY, Conj conj:Yan, Thm t:Yan-conj)',summary='Chan-Pak Theorem t:Yan-conj resolves Yan Conj. 3.40 in the source itself: (i)<=>(ii)<=>(iv) for all loopless matroids, and a loopless binary matroid where (iii) holds but not (ii) (so the full conclusion fails). Zero credit.'),
364351:dict(outcome='PARKED_STRUCTURAL',review_depth='abstract v3 (SIDMA)',summary='Shellability of k-cut complexes of all grid graphs for 3<=k<=mn-3; source proves 2xn, 3xn cases; general case topological; adjacent to 373304 family. Parked.'),
364355:dict(outcome='PARKED_ASYMPTOTIC',review_depth='abstract',summary='Matrix-set filling conjecture is asymptotic in n (|X_i|>=q^{cn^2}, mu(c)); no finite route.'),
364471:dict(outcome='PARKED_FAMOUS_OPEN',review_depth='abstract',summary='Griggs nested chain decomposition conjecture for B_n (famous, open); source studies Schur positivity of distributive lattices. Parked.'),
364559:dict(outcome='PARKED_IMPRECISE_STATEMENT',review_depth='source TeX read (Sec. 6 conjectures)',summary='The coefficient pattern is specified only by an image (Figure ILCFig18_pattern); the textual statement is not precise enough for a literal resolution. Parked.'),
364626:dict(outcome='PARKED_STRUCTURAL',review_depth='abstract; TeX located',summary='Finiteness of connected graphs with odd metamour (2-distance) period for every odd k; period 3 classified (C7, C9). Needs a classification or an infinite family; no tractable route found. Parked.'),
364642:dict(outcome='ENDPOINT_FAILURE_ZERO_CREDIT',review_depth='source TeX read (Conjecture conj2i, Thm thm:conj); citing paper arXiv:2509.17705 read (proves 8n+7); numerical check',
 summary='Open cases were 8n+2, 8n+4, 8n+6. Exact series computation (n<=240, i<=4, odd r<=9) finds the 8n+4 congruence mod 2^{2i+4} FALSE exactly at i=1 for every tested r: OPT_2(4)=32=2^5 (need 2^6), OPT_6(4)=1056=2^5*33; it holds for i=2,3,4 in range, as do 8n+2 and 8n+6. Failure only at the smallest parameter i=1: zero-credit endpoint correction (370483 precedent; adjacent family).',
 computation='scripts/opt364642.py, opt364642b.py; logs/opt364642.log'),
364883:dict(outcome='PARKED_PARTIAL_VERIFICATION',review_depth='source TeX read in full (Conjectures 1-4, Thms ThmY, genefirstn1to2NEW, tI0); web search; Shearer table URL now redirects (unavailable)',
 summary='Exact bitmask exact-cover computation: regular (I,J,IJ)-DGR exists iff I>=2 (J=3), I>=3 (J=4), I>=4 (J=5,6), and I=5,6,7 regular for J=7 (I=4 not, exhaustive). Since regularity is closed under addition, regularity propagation holds for all I when J<=6. No counterexample; general proof not found.',
 computation='scripts/dgr.py, dgrreg.py; logs/dgr-regular*.log'),
364884:dict(outcome='PARKED_PARTIAL_VERIFICATION',review_depth='source TeX read in full; same as 364883',
 summary='Extension conjecture verified exhaustively at the regularity thresholds and nearby: (J,I)=(3,2),(3,3),(4,3),(4,4),(5,4),(6,4): every Golomb J-ruler A1 in [(I+1)J] extends (68,190,958,2984,14126,31158 rulers). No counterexample. Pair with 364883 (one source; a variant earns nothing).',
 computation='scripts/dgr.py, dgrfast.py; logs/dgr-extend-*.log'),
}
EXTRA={364884:('364883-abs','eprint/364883','prior/shearer-dgrtable'),364883:('prior/shearer-dgrtable',),364116:('prior/2507.09304-abs','eprint/prior-2507.09304'),364642:('prior/2509.17705-abs','eprint/prior-2509.17705')}
out={}
for i in sorted(D):
    e=ex[str(i)]
    o={'mathdb_id':i,'title':e['title'],'source_url':e['source_url'],'provenance':e['provenance'],'source_receipts':receipts(i,EXTRA.get(i,()))}
    o.update(D[i]); o.setdefault('credit_claim','none')
    out[str(i)]=o
assert len(out)==20 and set(map(int,out))==set(json.loads((L/'reservation.json').read_text())['ids'])
(L/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False)+'\n')
print('wrote',len(out))
