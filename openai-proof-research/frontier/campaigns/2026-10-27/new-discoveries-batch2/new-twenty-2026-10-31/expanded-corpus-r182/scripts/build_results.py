import json, pathlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'extracted.json').read_text()); rec=json.loads((L/'outputs/fetch-receipts.json').read_text())
def receipts(prefixes):
    out={}
    for r in rec:
        if any(r['id'].startswith(p) for p in prefixes) and 'status' in r:
            out[r['id']]={k:r[k] for k in ('url','status','sha256','utc')}
    return out
D={}
def put(i,outcome,depth,summary,computation=None,credit='none',extra=()):
    i=str(i); e=ex[i]
    D[i]=dict(mathdb_id=int(i),title=e['title'],source_url=e['source_url'],provenance=e['provenance'],
              source_receipts=receipts([i+'-abs','eprint-'+i]+list(extra)),outcome=outcome,review_depth=depth,
              summary=summary,computation=computation,credit_claim=credit)
put(351804,'CANDIDATE_COUNTEREXAMPLE_HIGH_CREDIT_RISK',
 'arXiv v1 (only version) TeX read: Definition 1.1 (G\', G\'\', G\'\'\'), Theorems 2.5, 2.7, 2.8, 2.9, Conjecture 2.10 (line 235); journal version Oper. Matrices 18 (2024) 319-333 full PDF read: Section 3 (Lemma 3.6, Theorem 3.7, Remark 3.8); 3 web searches; Lean Pool, Omega, OpenAI/math and GitHub screens',
 'Fixed-strong-component reading refuted by an exact 5-vertex certificate. G* has arcs 0->1,0->2,1->0,1->2,1->3,2->0,3->0, with out-degrees (2,3,1,1) and v1 = 1. G = G* + 0->4 lies in G_5^4; G\'\' = G* + 1->4. At alpha = 1/4: charpoly(4A(G)) = s(s^4-8s^3+4s^2-24s+27) is negative at 781/100, while 4A(G\'\') x <= (2309/296) x for x = (671,1000,296,296,1). Hence rho_{1/4}(G) > 781/400 > rho_{1/4}(G\'\'). Mechanism: diagonal Perron sensitivity x_j y_j, not out-degree. Exhaustive m <= 4, E <= 3 sweep: 204 violating G* at E = 1, none inside the source-proved alpha range. Journal version: replaced the conjecture by Theorem 3.7 (K_n^m is the global maximiser, i.e. the global reading is proved) and Remark 3.8 (the fixed-G* question, which this example answers negatively). See CANDIDATE-351804.md and the UNCOMPILED lean/AalphaNonStrongCounterexample.lean.',
 'scripts/aalpha_search.py, aalpha_detail.py, aalpha_cert.py, aalpha_cert2.py, aalpha_rangecheck.py, aalpha_perron.py; logs/aalpha-*.log',
 credit='candidate only; HIGH risk (journal Thm 3.7 resolves the global reading; generic Perron-perturbation mechanism; niche)',extra=('351804-oam','oam-351804'))
put(351504,'PROVED_BY_ROUTINE_BRIDGE',
 'arXiv v1 TeX read in full for definitions (H-length, (k,H)-kernel, closure; lines 80-130), Theorems for quasi-transitive and 3-quasi-transitive digraphs and the conjecture (line 356); kings paper arXiv:1206.1897 abstract + TeX (Lemma k-1-dom-comp, line 217) read; structure literature (arXiv:2006.06333) noted; web search',
 'The conjecture is TRUE in full scope (k >= r+2), for every H-colouring. Proof: take S = one vertex per terminal strong component T, chosen as a reversed (r+1)-king of D[T] by Galeana-Sanchez, Hernandez-Cruz and Juarez-Camacho (Discrete Math. 2013; reversal preserves r-quasi-transitivity). A path between different strong components has length <= r-1 (geodesic lemma, also Lemma k-1-dom-comp there). Absorbing paths of length <= r+1 <= k-1 have H-length <= k-1, and distinct terminal components are mutually unreachable. This is a one-paragraph bridge from a 2013 paper by the same first author, so zero credit is expected (outputs/351504-bridge-proof.md). The exhaustive search was skipped because the proof makes it moot.',
 credit='none (routine bridge from published lemmas)',extra=('351504-kings',))
put(345726,'PARKED_RANDOM_SEARCH',
 'arXiv v1 abstract + TeX (conjecture statement) read; web search (Bang-Jensen et al. Conjecture 7 still open; Gu-Gutin-Li-Shi-Tao 10-vertex no-good-pair example concerns 2-arc-strong digraphs)',
 'Prescribed-roots conjecture (3-arc-strong, alpha = 2). Complete branching checker: all parent functions, plus the complement in-branching test. Positive control: 2-arc-strong prescribed-root failures are found at n = 6, consistent with the source. Random arc-minimal 3-arc-strong digraphs with alpha exactly 2 had a good pair for EVERY (s,t): n = 6 (62,554), n = 7 (31,213), n = 8 (16,831), n = 9 (9,448). No counterexample, no proof.',
 'scripts/branch_search.py; logs/branch-*.log')
put(352363,'SOURCE_REFUTED_AS_PRINTED',
 'arXiv v2 TeX read: Conjecture k-conn (line 75), Theorem RWZ, the N_9 matrix, lines 104-110',
 'The MathDB statement is exactly the Reid-Wu-Zhou conjecture (Conj. 1.1). The source states that it fails at k = 4 for the 9-element N_9 (9 >= 2(k-1)) and that RWZ disproved it for every k >= 5 by (2k+1)-element examples; the surviving question (|E(M)| != 2k+1, and the vertical-connectivity Problem 1.2) differs. Zero credit; matroid enumeration is outside capped-Python scope.')
put(352370,'PARKED_DEEP',
 'arXiv v3 TeX read (k-multiple tree definition, Conjecture of Kriesell, closing conjecture/questions); Illingworth-Powierski-Scott-Tamitegama arXiv:2205.04984 (EJC 2023) TeX read: Question qu:general and line 1984',
 'A uniform bound c independent of k is still open per the EJC 2023 follow-up ("It would be particularly interesting to resolve Horsch\'s conjecture ... uniform upper bound on the c_k"). Known: c_2 <= 4 (IPST) and c_k = O(log k) (Horsch). A statement uniform over all k has no finite certificate. Parked.',extra=('352370-ipst',))
put(371727,'PARKED_STRUCTURAL',
 'arXiv v1 TeX read: monotone partition, box graph, hev-property, Theorem thm:box and forest case (lines 398-470, 842-863), Conjecture (line ~870), 3-ring remark',
 'A clique-width bound f(k,x) over all graphs with monotone clique partitions. Infinite structural statement; clique-width is not computable in a capped lane, and 3-rings (Hoang-Trotignon 2024) show cycles are essential. No finite certificate route. Parked.')
put(345158,'PARKED_DEEP',
 'arXiv v2 (JCTA) TeX read: Conjectures conj:weak (line 130) and conj:strong (line 509); web search for follow-ups; OpenAI/math Ryser counterexample preprints (Sept 2026) README + paper.tex screened',
 'Exact value Ryser(r,t) = floor((r-t)/2)+1 for t >= 2 (the source\'s own Conj. 1.6). Proved for r <= 3t-1, and the weak form for r <= 36t/7 - 5; first open case r = 3t (t = 2, r = 6). The 2026 OpenAI Ryser counterexamples are intersecting (t = 1), (q+1)-partite constructions and do not transfer (padding with common vertices gives tau = 1). Exhaustive (6,2)-graph search infeasible. Parked.',extra=('openai-ryser',))
put(345188,'PARKED_PROBABILISTIC',
 'arXiv v2 abstract + comments read (Theorem 5 gives a 1/2n lower bound)',
 'Uniform delta > 0 for the connectivity probability of uniform unlabelled bridge-addable graphs: a probabilistic statement uniform in n; finite computations cannot refute or prove it. Parked.')
put(345562,'PARKED_NO_FINITE_CERTIFICATE',
 'arXiv v7 TeX read: subrow, S-integral and k-regular definitions (lines 57-138), Theorem infty',
 'With sigma(n) = s_1+...+s_n, the S-integral of the subrow S_{a,b} is S_{sigma(a-1)+1, sigma(b)}. So infinity-regularity of (a,b) means sigma^h(b) and sigma^h(a-1) have the same parity for all h >= 0. Nonexistence is an infinite statement about the Kolakoski dynamics (it implies recurrence-type consequences). No finite certificate in either direction. Parked.')
put(345642,'PARKED_KNOWN_PARTIAL',
 'arXiv v1 TeX read (Conjecture 5.1, Theorems 1.3-1.5); web searches: Yuan, CMR 2022 (15 <= k1+k2 <= 30); Leung-Zhang arXiv:2605.09871 (Woldar, k1 = 0) abstract',
 'Coprime splitter conjecture. For k1+k2 <= 30 the published classification (m in {k1+k2+1, 2k2+1}) forces coprime splitters: |S| = 1, or for |S| = 2 a non-unit s makes sM lie in the m/d - 1 < k2 nonzero multiples of d. For k1 = 0 it follows from the 2026 Leung-Zhang proof of Woldar\'s conjecture. A counterexample needs k1+k2 >= 31 and a nontrivial purely singular splitting, which would also refute Zhang-Ge; out of scope. Parked.')
put(352072,'PARKED_SDP_ANALYTIC',
 'arXiv v1 TeX read: Conjecture conjecture-monique (line 1029), Theorem theoGLstrong (holds for r <= min(6, alpha-1) and r = 7 = alpha-1), Conjecture conjisolated (disproved by the source), lines 120-240',
 'The displayed Gvozdenovic-Laurent bound (eq-monique) is distinct from the isolated-node conjecture the source disproves; its status remains open beyond r <= 6. It is a semidefinite-hierarchy inequality over all graphs: there is no SDP solver or numpy in this lane, and Lean cost is prohibitive. Parked.')
put(352492,'PARKED_DEEP',
 'arXiv v4 (Oct 2025) TeX read: Definition def:GS (A_GS = vectors whose first nonzero coordinate is 1), Definition def:hop, Proposition prop:GSnoHOP (p = 3), line 1187 conjecture for p > 3, Appendix app:no4hop',
 'Still conjectured in v4 for p > 3. A refutation needs unbounded HOP_2 for some p uniformly in n (an infinite construction), while a proof needs a case analysis generalising the "tedious" p = 3 appendix. No finite certificate either way; deferred.')
put(352585,'PARKED_LARGELY_SETTLED',
 'arXiv v6 (DMTCS 2023) abstract; Cichacz survey arXiv:2410.22245 TeX read (Theorems SK, SK2, Muyesser-Pokrovskiy, Conjecture 3.4 still open); web search',
 '3-ZSPP for |I| > 1: proved for 2-groups (source), for all large orders (Muyesser-Pokrovskiy) and as 4-ZSPP for all such groups (Cichacz-Suchan); only finitely many small orders remain (and in Cichacz-Suchan 2022 only the rho = 5 mod 6 case). Family warning (zero-sum family with 365570-365572). Parked.',extra=('365570',))
put(352587,'PARKED_FAMILY',
 'arXiv v6 abstract and statement; family warning',
 'Equal-sum partitions of Z_{2^n} (equivalent to complete multipartite distance magic). In the warned zero-sum family; no route beyond small cases. Parked.')
put(365570,'SOURCE_REFUTED',
 'Survey arXiv:2410.22245 TeX read (lines 112-122: "Cichacz and Suchan showed recently that Conjecture conjectureT is false in general"; Theorem Skol)',
 'Tannenbaum\'s conjecture is false in general (Cichacz-Suchan): it holds iff |I(Gamma)| in {3, |Gamma*|}. MathDB itself records the disproof. Zero credit.')
put(358587,'PUBLISHED_RESOLUTION_AND_CREDITED_FAMILY',
 'arXiv v1 abstract read; prior campaign screening (root-nearline-r1/screening.md) recorded the 2212.03026 classification',
 'Circulant nut graphs exist iff 4 | d, 2 | n, n >= d+4 (d = 4 mod 8) or n >= d+6 (8 | d), (n,d) != (16,8) (Damnjanovic and coauthors, arXiv:2212.03026). The literal circulant statement thus fails for 8 | d at n = d+4, already in the literature, and the Cayley version is proved by the source. Credited 365943 family. Zero credit.')
put(352396,'SOURCE_SETTLED',
 'arXiv v3 abstract (Advances in Combinatorics 2024)',
 'Dhar proves the Hickman-Wright Kakeya set conjecture over Z/NZ for general N (the source itself). Zero credit.')
put(352628,'PARKED_FAMOUS',
 'arXiv v5 abstract (LAA) read',
 'The 3-dimensional Dinitz (list Latin cube) conjecture is a famous open problem, raised among the source\'s closing open problems; no finite certificate route at size n^2 lists. Disposed quickly per the brief.')
put(352856,'PARKED_FAMOUS',
 'arXiv v1 abstract read (source is a local antimagic paper citing the conjecture)',
 'Hartsfield-Ringel antimagic tree conjecture: famous and long-standing (the lane did not survey the small-tree verification literature); adjacent to the credited 354228 local antimagic family. Disposed quickly per the brief.')
put(359400,'PARKED_FAMOUS',
 'arXiv v1 abstract read',
 'Oxley\'s 1992 CCI conjecture: the source proves k <= 7; regular matroids by Kingan-Lemos. Deep matroid statement with no capped-Python route. Disposed quickly per the brief.')
ids=set(str(x) for x in json.loads((L/'reservation.json').read_text())['ids'])
assert len(D)==20 and set(D)==ids, (len(D), ids^set(D))
(L/'results.json').write_text(json.dumps(D,indent=1,ensure_ascii=False)+'\n')
print('wrote',len(D))
