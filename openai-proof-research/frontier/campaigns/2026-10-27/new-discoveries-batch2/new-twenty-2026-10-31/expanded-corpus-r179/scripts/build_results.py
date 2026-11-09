import json, pathlib, hashlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'extracted.json').read_text()); rec=json.loads((L/'outputs/fetch-receipts.json').read_text())
def receipts(prefixes):
    out={}
    for r in rec:
        if any(r['id'].startswith(p) for p in prefixes) and 'status' in r:
            out[r['id']]={k:r[k] for k in ('url','status','sha256','utc')}
    return out
D={}
def put(i,outcome,depth,summary,computation=None,credit='none',extra_receipts=()):
    i=str(i); e=ex[i]
    D[i]=dict(mathdb_id=int(i),title=e['title'],source_url=e['source_url'],provenance=e['provenance'],
              source_receipts=receipts([i+'-abs','eprint-'+i]+list(extra_receipts)),outcome=outcome,review_depth=depth,
              summary=summary,computation=computation,credit_claim=credit)
put(353377,'PARKED_SOURCE_VERIFIED_RANGE',
 'arXiv abs v1 (only version) + TeX read: Conj. conj:4 (lines 134/582), definitions of SNP and generalized polymatroid (Def. def:gpolymatroid), verification remark (line 155); web search for later resolutions',
 'Generalized polymatroid / SNP conjecture for Grothendieck polynomials (Meszaros-Setiabrata-St. Dizier). Authors tested it for all w in S_8; it strengthens Meszaros-St. Dizier Conj. 5.1 and is implied by a Lorentzian conjecture (source line 594). Only special cases known (Grassmannian, fireworks, later bubbling results, e.g. arXiv:2602.02448 describes it as open). No Python-feasible route beyond S_8 in this lane; no proof mechanism found.')
put(353461,'PARKED_COMPUTATIONALLY_VERIFIED_NO_PROOF',
 'arXiv v3 TeX read: Conjecture path1 (line 1352), Reiner Theorem ReinerBraid, Lemma casesproved, Theorem mainresult; 3 web searches (no later resolution found); Lean Pool/GitHub screen',
 'Elder nonnegative-excess conjecture A(sigma)=|R(sigma)|-sum d_B >= 0 (equivalently: the expected number of braid moves of a uniform reduced word is <= 1). Exact weak-order DP (B(s)=sum_{k in D_R} B(s s_k)+2 sum_{k,k+1 in D_R} N(s w0_{k,k+1})) verifies A>=0 for ALL sigma in S_n, n<=9 (362880 permutations at n=9), reproduces Reiner equality at w0, and shows equality holds exactly at the longest elements of interval parabolics (21 at n=8, 28 at n=9). Near-extremal ratio B/N: w0 s_1 with 0.988235 at n=9 (approaching 1 from below). Stronger per-Coxeter-Knuth-class version (braids <= class size) verified for every CK class with n<=6 (1007 classes), equality only for interval w0 classes. Reiner\'s proof uses the cyclic (promotion) symmetry of R(w0), which fails for general sigma; no proof found.',
 'scripts/braid_excess.py, braid_excess2.py, braid_data.py, braid_ck.py; logs/braid_excess*.log')
put(353562,'PARKED_ASYMPTOTIC',
 'arXiv v3 abstract (EJC accepted) + statement',
 'Constant-depth decision-tree conjecture asserts existence of k_0(q,d) for Boolean degree-d functions on J_q(n,k): an eventual/asymptotic statement with no finite refuting certificate available from small cases; source gives only examples (n,k)=(6,3),(8,4). Disposed quickly.')
put(353814,'PARKED_KNOWN_OPEN_RANDOM_SEARCH',
 'arXiv v3 TeX read (lines 174-192, 493-512, 560): status paragraph and Cor. cor:equitable; EGRES open problem cited',
 'Equitability conjecture (EGRES open problem). Known for base orderable (Fekete-Szabo), graphic/hypergraphic (Kiraly), sparse paving (Bonin), split matroids (source Cor. cor:equitable); implied by Gabow\'s and by Hamidoune\'s conjectures. Random sparse ternary rank-5 vector matroids E=A u B: 34,710 tested, all equitable (exhaustive over all X). No counterexample, no proof.',
 'scripts/equitable.py')
put(353833,'PARKED_PARTIALLY_SETTLED_IN_PRIOR_LITERATURE',
 'arXiv v2 TeX read in full (note); Jafari arXiv:2009.10676 v2 Theorem thm1 read; Shaebani arXiv:2206.00836 v1 read (Conj. Almost, Thms Forrgeqs1/directrs/inversers); web search',
 'Daneshpajouh weaker conjecture chi(KG^r(F_almost-r-stab)) >= ceil(cd_r(F)/(r-1)). For r a power of 2 it already follows from Jafari 2020 Thm 1 (s=r multiple of r, ecd^r >= cd_r), which predates the note; Shaebani 2022 generalizes it to Conjecture Almost (r>=s), still open. r=3 search: F = all pairs at distance <=2 plus random maximal almost-3-stable families A with no 3 pairwise disjoint members (so chi=1), n=8,10: cd_3 never reached 3 (~10^4 families). Any r=2 or power-of-2 result is zero credit (Jafari).',
 'scripts/kneser_r3.py',extra_receipts=('353833-',))
put(353965,'PARKED_ANALYTIC',
 'arXiv v2 (2024) abstract read',
 'Optimal error term D|A|^{1-1/d} in Conlon-Lim sums of linear transformations: analytic additive-combinatorics bound for all finite A in Z^d; source proves the o(|A|) two-summand case. No finite certificate; disposed.')
put(354031,'SOURCE_REFUTED',
 'arXiv v1 abstract read',
 'The Nowakowski-Rall conjecture i(GxH) >= i(G)i(H) is disproved by the source itself (Kuenzel-Rall), with min{i(G),i(H)}-i(GxH) arbitrarily large. Record is a refuted conjecture; zero credit. Also adjacent to credited domination families.')
put(354152,'PARKED_DEEP',
 'arXiv v1 abstract read',
 'Monadic dependence characterization of FPT FO model checking (Twin-width VIII context): flagship structural/complexity conjecture (hardness side handled by flip-breakability work; tractability open). Disposed quickly per brief.')
put(354240,'PARKED_COMPUTATIONALLY_VERIFIED_NO_PROOF',
 'arXiv v2 TeX read: definitions A_t(n,d), A_t(d), Thms Par17/AGNS22, Conjecture con:TM_bound (line 1169), computation section (Prop. progressions_in_subwords, filters), verified range d<=2^12+1; web search (no resolution found); Lean Pool/GitHub screen',
 'Sobolewski Thue-Morse bound A_t(d) <= d+5 with equality iff d=2^k-1, k even. Exact method: any AP of span < 2^K lies in (t(q)^x)(t(q+1)^x), x=t[0,2^K); since 00,01 occur in t, windows x+xbar and x+x suffice; bit i of M=~(W^(W>>d)) marks t(i)=t(i+d); stride-d AND chains by doubling. Verified for ALL odd d <= 2^15+1 = 32769 (8x the authors\' range; even d via A(2d)=A(d)): no counterexample; equality exactly at d=3,15,63,255,1023,4095,16383; d=32767, 32769 covered by the Parshina / AGNS theorems (A=d+1). For 20001<=d<=32765 survivors with A>=400 were certified A <= d/4. No proof for all d (digit-carry dynamics; the source author left it open).',
 'scripts/tm_ap.py (v1), scripts/tm_ap2.py (v2); logs/tm_ap*.log; resource incidents in logs/incident-background.txt')
put(354402,'SOURCE_SETTLED',
 'arXiv v2 abstract read',
 'Twin-width VII itself constructs (via Osajda) a class of finite graphs with unbounded twin-width containing 2^{O(n)} n! graphs on [n]: a hereditary closure of it is small with unbounded twin-width, so the smallness characterisation conjecture is refuted in the source. Zero credit.')
put(354598,'PUBLISHED_RESOLUTION',
 'arXiv v1 TeX read (definitions of R(G,p), L(G,p), spectral gap, Theorems simplex_repeated/crosspolytope_spectrum, final Conjecture line 1343); Jung-Lew arXiv:2504.01181 abstract read; web search',
 'Repeated-point scaling conjecture is reported resolved by Jung-Lew (arXiv:2504.01181, 2025) as a special case of their blow-up spectrum relation. Lane analysis (not credited): the fibre decomposition (fibre-constant vectors: k L(K_n,p); fibre-zero-sum vectors: k M_u (x) I_{k-1}, M_u = sum_v d_uv d_uv^T) shows lambda(K_kn,p^k)/k is the (c+1)-th smallest element of spec L(K_n,p) u (k-1)*U_u spec M_u, c=C(d+1,2); for n >= d+1 this is independent of k>=2 (a short proof). The literal statement fails in the degenerate regime 2n <= d, e.g. d=6, n=2, k=3, p=(0,e_1): spec L(K_4,p^2)={0^21,2,2,4} gives lambda=2, while L(K_6,p^3) has 31 zero eigenvalues so lambda=0 != 3 -- a zero-credit domain correction (|V| <= d, outside the source\'s standing assumption |V|>d).',
 credit='none (published resolution; degenerate-domain correction only)',extra_receipts=('354598-',))
put(354654,'PARKED_NONFORMAL',
 'arXiv v3 abstract read',
 'Conservative-extension domination conjecture for propositional proof systems: tied to nonexistence of optimal proof systems (open complexity questions); no finite object. Disposed.')
put(354937,'PARKED_EXHAUSTIVE_SMALL_CASES',
 'arXiv v2 TeX read: configuration definitions, cups/caps, interweaved (Def. def:inter-laced), laced (Def. def:laced), Theorem thm:main-lemma (k=2) and Conjecture conj:interweaved; Lean Pool ErdosTuzaValtr project (jcpaik/erdos-tuza-valtr) read: formalizes only the k=2 main theorem; SoCG 2025 follow-up noted',
 'Baek mutually interweaved laced-cup conjecture. Exact reduction: replacing cups by caps only removes laced cups and n-cups, and every 4-cap-free cap set lies in the cap set of a pair labelling s (cap(xyz) iff s(xy)=B, s(yz)=A); further WLOG s(0,.)=B, s(.,N-1)=A; exact forward-check pruning. Exhaustive: n=4 all k; n=5: k=1 (101376 labellings), k=2 (939008; reproduces Baek), k=3 first open case (5,799,936 labellings unreduced in 4 chunks; 4096 reduced) -- all satisfy the conjecture; k=4 is the maximum size (source). n=6 (N=13,14) too large for capped Python; local searches (n=6,k=3) found nothing below 3. No counterexample, no proof.',
 'scripts/laced.py, laced_search.py, laced_exh.py, laced_exh2.py, laced_ls.py, laced_ls2.py; logs/laced-*.log')
put(355044,'PARKED_ANALYTIC',
 'arXiv v1 abstract + conjecture statement',
 'Convex lower-bound conjecture for optimal resistor networks: a(x), b(x) are asymptotic optimal-network functions (limits over n) and f is a maximal convex minorant; no finite certificate. Disposed.')
put(355099,'PARKED_DEEP',
 'arXiv v3 TeX read: Conjecture optim (line 125), optim2, remark that both are implied by the Aharoni-Berger conjecture ahconj',
 'Rainbow base factorization for (k-1)-bounded partitions: the source notes it is implied by the Aharoni-Berger conjecture; first open case k=3 (classes of size 2). Deep matroid-intersection-type statement; disposed quickly per family warning.')
put(355117,'PARKED_DEEP',
 'arXiv v2 abstract (SIDMA 2023) + statement',
 'Mkrtchyan-Vardanyan edge-incidence statement is equivalent to the Fan-Raspaud conjecture (per source); famous open problem. Disposed.')
put(361284,'PARKED_DEEP',
 'arXiv v1 abstract (survey) + web search',
 'Aharoni-Howard bipartite rainbow matching conjecture (cited in an eigenvalue/factor survey) belongs to the Aharoni-Berger rainbow matching family; famous, deep. Disposed quickly per brief.')
put(361332,'SOURCE_REFUTED',
 'arXiv v1 abstract read',
 'The source (Ghanbari-Hartman-Jelinek-Pokorna-Samal-Valtr) disproves the Gago-Coronicova-Hurajova-Madaras conjecture and characterises BUGs with betweenness <= 9/10 (values l/(l+1), l<=9). MathDB record itself says refuted. Zero credit; adjacent to parked 350694 family.')
put(370547,'PARKED_DEEP',
 'arXiv v2 (Nov 2025) abstract read',
 'k-Roudneff conjecture for oriented matroids: source proves Lawrence OM cases, low ranks by computer and an asymptotic version; famous (1991) and deep. Disposed quickly per brief.')
put(382089,'PARKED_RANDOM_SEARCH',
 'arXiv v1 TeX read: Section on properties R, R+, P, P+ (lines 391-435), Theorems for graphic, paving and spike matroids, consequence at line 613',
 'Berczi-Schwarcz alternating path covering conjecture (property P+). Reduction: contract A cap B, restrict to A u B. Tested random vector matroids [I|X] (dense and sparse) over GF(2), GF(3): rank 4 binary 51,058; rank 5 binary 22,466; rank 5 ternary 15,863 dense + 19,224 sparse; rank 6 ternary sparse 3,380; every one has an alternating ordering in which every circuit contains two consecutive elements. Proved by the source for graphic, paving and spike matroids. No counterexample.',
 'scripts/pplus.py')
assert len(D)==20 and set(D)==set(str(x) for x in json.loads((L/'reservation.json').read_text())['ids'])
(L/'results.json').write_text(json.dumps(D,indent=1,ensure_ascii=False)+'\n')
print('wrote',len(D))
