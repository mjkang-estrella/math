"""Build results.json (20 ID-keyed entries) from extracted.json provenance plus lane dispositions, and
artifact-hashes.json for all lane files.  Usage: finalize.py LANE"""
import sys, json, pathlib, hashlib
D = pathlib.Path(sys.argv[1]).resolve()
ex = json.loads((D / 'extracted.json').read_text())
H = lambda p: hashlib.sha256((D / p).read_bytes()).hexdigest() if (D / p).exists() else None
R = {}
def put(i, outcome, depth, mech, coverage, receipts, notes, lean='none (no candidate)'):
    R[str(i)] = {'outcome': outcome, 'review_depth': depth, 'mechanism_and_prior_art': mech,
                 'finite_search_coverage': coverage, 'receipts': receipts, 'remaining_lemmas_or_notes': notes,
                 'lean_endpoint': lean}
put(353231, 'EXCLUDED_PUBLIC_LEAN_REFUTATION (independently rediscovered)',
    'Literal statement; EPRS arXiv:2108.12443v2 Section 5 (Conjecture 5.4(b), verified a+s<=12) and Elizalde-Sagan arXiv:2201.03044v1 Conjecture 4.8 read; Mertin-Poznanovic arXiv:2406.02493 Section 5 read (Conjecture 5.1, still open there, checked a+t<=10, (2^9), (8^3)).',
    'MathDB F(beta), beta=(k-1,k,...,k,k-1) odd parts = EPRS F̆(k^t). Lane exact orbit search found a violation at F̆(3^11), n=32: a rowmotion orbit of length 237 with sum |I| = 3810 != 16*237 (and its mirror with 3774). Verified by an independent toggle-based implementation that also checks the EPRS definition rho(I)=P-upset(max I). BUT a public GitHub repository Aurantium-47/fence-rowmotion-counterexample (created 2026-10-13, HEAD bef0bd6c, "Document kernel verification") already gives this 32-element fence, the 237-state orbit, an exact checker and a Lean formalization. Zero credit.',
    'All (a,t), t odd >=3, a>=2, a+t<=12: no violation (consistent with authors). (2,13), (8,5), (6,7), (4,9): no violation. (3,11): violating orbits (first violation layer a+t=14).',
    ['sources/2108.12443v2.html', 'sources/2201.03044v1.pdf', 'sources/2406.02493.pdf', 'sources/gh-fence-repo.json', 'sources/gh-fence-head.json', 'logs/fence-a3-t11.log', 'logs/fence-verify-3-11-a.log', 'logs/fence-sweep-le12.log'],
    'Prior public counterexample with Lean formalization predates this lane; do not pursue.')
put(382066, 'PARKED_OPEN_VERIFIED_TO_N10 (Lean-infeasible endpoint)',
    'Literal statement; arXiv:2302.00343v1 Definition 1.1, Section 6 (Theorem 6.4, Remark 6.7, Prop 6.10, Thm 6.12, Thm 6.16, Def 6.17, Thm 6.19, Conjecture 6.20) read. Web search: no later resolution found.',
    'Exact combinatorial reformulation: A_G flag-accurate iff a contraction sequence exists whose simple quotients are chordal with exponents (PEO earlier-neighbour counts) equal to the initial segments of exp(A_G) (Stanley/Edelman-Reiner freeness = chordality; restriction = contraction). Partial proof route: contracting an edge at a simplicial vertex u deletes u and removes exponent deg(u), and max exponent = omega-1, so repeated deletion of simplicial vertices lying in maximum cliques suffices; by hand this fails for the strongly chordal Q_4 with outer triangles on edges 01, 02, 03 (no simplicial vertex in its unique K_4), which the search nevertheless finds flag-accurate via other contractions. No general proof found.',
    'ALL connected strongly chordal graphs up to isomorphism: n<=9 (1,2,5,15,57,263,1497,10278) and every one-vertex clique extension of all 10278 graphs on 9 vertices (all connected strongly chordal graphs on 10 vertices; 8 chunks, ~245k chunk-level checks): no graph fails flag-accuracy. Controls: source Prop. 6.10 graphs Q_4(1^6), Q_4(2^6) detected as NOT flag-accurate; 3-sun flag-accurate (Cor. 6.9).',
    ['sources/2302.00343v1.pdf', 'logs/sc-flag-n9.log', 'logs/sc-flag-controls.log'] + [f'logs/sc-flag-n10-c{c}of8.log' for c in range(8)],
    'A counterexample would need Terao factorisation / freeness theory in Lean (absent from mathlib); a proof would need the same. Next lemma to try (unchecked): every connected strongly chordal graph has an edge whose contraction is chordal, removes exactly one maximal exponent, and stays strongly chordal; that would give a proof by induction.')
put(353252, 'PARKED_NUMERICALLY_TIGHT',
    'Literal statement; Barrett-Evans-Hall-Kempton arXiv:2201.04225v1 Section 4.3 (Definition 4.7, Theorem 4.8, Conjecture 6) read.',
    'Random-restart local search over weights in [0,1] converges to x+y-2xy/n = 1 exactly (SE(s) family), never below. Counterexample would be Lean-cheap (rational Rayleigh-quotient upper bounds on lambda_2 of G and G^c plus monotonicity), but none found. A proof needs a strengthened weighted Laplacian-spread argument (u*v <= n(n-2)/4 with u = n/2 - lambda_2, v = lambda_n - n/2), beyond the spread bound (n-1).',
    'n=5: 20 restarts x 1500 steps; n=6: 12 restarts x 1200 steps; minimum 1 - 1e-14 (equality family).',
    ['sources/2201.04225v1.pdf', 'logs/spread-n5-s1.log', 'logs/spread-n6-s2.log'], 'Open; analytic.')
put(353446, 'PARKED (literal text misprinted; intended rule holds in tested range)',
    'Literal statement; Wang-Krattenthaler arXiv:2201.12415v1 Conjecture 11.2 and Section 11 read; Bhatnagar-Schlosser arXiv:1902.04447 noted via search.',
    'Literal range 0<=l<K/2 includes 2l+1=K, so residue 0 is declared nonpositive, contradicting b_0=1: a zero-credit misprint. Intended rule recovered from data: write m = +-j a (mod K), 0<=j<=(K-1)/2; b_m<=0 iff j odd. Sweep found no violation.',
    'K odd 3..15, all admissible a, n<=14; K odd 17..41, all admissible a, n<=8: no violation of the intended rule.',
    ['sources/2201.12415v1.pdf', 'logs/iks-K5-a1.log', 'logs/iks-K7-a1.log', 'logs/iks-sweep-K3-15-n14.log', 'logs/iks-sweep-K17-41-n8.log'],
    'Open (asymptotic machinery of Wang-Krattenthaler expected to give large n); full proof analytic.')
put(353267, 'PARKED_OPEN (bounded exhaustive k=2 check)',
    'Literal statement; Camina-Cocke-Thillaisundaram arXiv:2201.04860v3 and Kishnani-Kulshrestha arXiv:2309.09010 introductions/theorem statements read.',
    'Open even for class 2 (best known P >= |G\'|^-1 |G|^-1). Exhaustive enumeration of all 2-variable word maps (relatively free group F_2(G)) on UT(4,2) (order 64, class 3): |F_2(G)| = 128 word maps, minimum positive fiber exactly 64 = |G| (bound attained, not violated). Control D16: 1024 maps, min fiber 16.',
    'UT(4,2) and D16 with k=2 only.',
    ['sources/2201.04860v3.pdf', 'sources/2309.09010.pdf', 'logs/aa-k2-UT4F2.log', 'logs/aa-k2-D16.log'], 'Major open conjecture; no mechanism.')
put(382086, 'EXCLUDED_ENDPOINT_MISPRINT (corrected form holds; probable published proof)',
    'Literal statement; Ballantine-Merca arXiv:2302.01253v1 Section 8.2 (Theorem 1.10, Conjecture 4) read; Ding-Sun arXiv:2403.11608 and arXiv:2609.25739 searched; JCTA 2024 paper "Some conjectures of Ballantine and Merca on truncated sums and the minimal excludant in congruences classes" is a title-level lead only (ScienceDirect denied, body unread).',
    'Literal (ii) strictness threshold (3k+2)(3k+3)/2 is false at the endpoint window (e.g. k=0, n=3: b6(3)-2b6(2)+b6(0)=0=beta_3); every failure lies in [(3k+2)(3k+3)/2, (3k+3)(3k+4)/2), matching the series statement "nonzero iff n >= (k+1)(k+2)/2" with truncation 3k+2. A zero-credit endpoint correction.',
    'N<=1500, k<=8; Theorem 1.10 sanity check passed; 135 literal failures, 0 outside the endpoint window.',
    ['sources/2302.01253v1.pdf', 'logs/bm-conj4-N1500-k8-classified.log'], 'Do not pursue.')
put(382085, 'EXCLUDED_PUBLISHED_PROOF',
    'Literal statement = Ballantine-Merca Conjecture 2 (arXiv:2302.01253v1 Section 8.2); Ding-Sun arXiv:2403.11608 Conjecture 1.8 and Section 5 read.',
    'Proved by O. X. M. Yao, J. Combin. Theory Ser. A 206 (2024) 105903, and again (with generalisation to l-regular partitions) by Ding-Sun arXiv:2403.11608 (Adv. Appl. Math. 2025).',
    'none needed', ['sources/2403.11608.pdf', 'sources/2302.01253v1.pdf'], '')
put(382049, 'EXCLUDED_TRIVIAL_CLASSICAL_FAILURE',
    'Literal statement; Mayhew-Probert arXiv:2301.03781v4 Sections 3-4 (Theorem 3.2, Conjectures 4.1-4.3) read.',
    'Conjecture 4.2 claims every chordal H is C(G) for a chordal G. By the source\'s own printed Theorem 3.2 (Szwarcfiter-Bornstein) and the classical identity K(chordal) = dually chordal (Brandstaedt-Dragan-Chepoi-Voloshin 1998), the 3-sun (chordal, not dually chordal) is not C(G). Exhaustive check: of the 58 connected chordal graphs on 6 vertices exactly one (the 3-sun) fails Theorem 3.2. A smallest classical example plus a printed source theorem: zero credit.',
    'All 58 connected chordal graphs on 6 vertices (Theorem 3.2 criterion).', ['sources/2301.03781v4.pdf', 'logs/chordal-cliquegraph-n6.log'],
    'Literal refutation is near-folklore; no credit.')
put(353175, 'EXCLUDED_PUBLISHED_PROOF',
    'arXiv:2201.00665v6 (Jeong) introduction read.',
    'Jeong [Jeo22] proved: X biconnected and FS(Cycle_n, Y) connected imply FS(X, Y) connected, settling Defant-Kravitz Conjecture 7.1; with the DK cycle characterisation (complement of Y a forest with coprime tree sizes) this is exactly the record.',
    'none', ['sources/2201.00665v6.pdf'], '')
put(353456, 'EXCLUDED_SOURCE_PROVES',
    'arXiv:2201.12650v3 Section 4 (Conjecture 4.1, Theorem 4.1) located.',
    'Garijo-Marquez-Robles prove the Lopez-Bracho et al. path conjecture affirmatively (Theorem 4.1; Results Math. 79 (2024) 122).', 'none', ['sources/2201.12650v3.pdf'], '')
put(353541, 'EXCLUDED_PUBLISHED_PROOF',
    'arXiv:2202.02821v1 Section 8 (Conjecture 1, Theorems 45 and 48) read; Yuen arXiv:2301.02517 abstract read.',
    'C. H. Yuen, "The critical groups of Adinkras up to 2-rank of Cayley graphs" (arXiv:2301.02517; Electron. J. Combin. 31(1) 2024, P1.38) proves the critical group is independent of the signature. Lane remark: L(NI+A) = N(N-1)I and switching a colour class negates all edges, so the SNF is symmetric and the conjecture is automatic unless 16 | N.',
    'none', ['sources/2202.02821v1.pdf', 'sources/2301.02517-abs.html'], '')
put(353211, 'EXCLUDED_SOURCE_PROVES',
    'arXiv:2201.02376v1 Section 2 (Conjecture 2) and Section 5.1 headings/proof sketch read.',
    'Source proves Conjectures 2-3 (and notes they follow from Bona-Ju-Yoshida Theorem 4).', 'none', ['sources/2201.02376v1.pdf'], '')
put(361703, 'EXCLUDED_PUBLISHED_REFUTATION',
    'arXiv:2402.01272v1 Section 3 (Conjecture 3.4, Theorem 3.5) read; earlier lane r89 notes reused.',
    'The weak real zero amalgamation conjecture is disproved in arXiv:2402.01272 (abstract and Theorem 3.5).', 'none', ['sources/2402.01272v1.html'], '')
put(382212, 'EXCLUDED_PUBLISHED_REFUTATION (by implication)',
    'arXiv:2305.07403v2 Section 7 (Conjectures 7.6, 7.7) and arXiv:2402.01272v1 Theorem 3.5 read.',
    'The strong conjecture (degree <= d amalgam, l=2) implies the weak one (take d = max degree); the weak one is refuted in arXiv:2402.01272, so the strong one is false.',
    'none', ['sources/2305.07403v2.pdf', 'sources/2402.01272v1.html'], '')
put(376393, 'EXCLUDED_SOURCE_PROVES', 'arXiv:2607.28295v2 abstract read.',
    'The source abstract states "We prove their conjecture" (ex(n, T box S) = Theta(n^{3/2}) for nontrivial trees T, S); asymptotic, not finite.', 'none', ['sources/2607.28295-abs.html'], '')
put(353583, 'EXCLUDED_PUBLIC_REFUTATION',
    'History screen: sol-fresh-discrete-discovery-r6 read current Omega Problems/gawron-ulas-2022-factorial-sign-conjecture-4-4.md, which refutes the universal assertion (m=3, k=2, negative progression 12s+38).',
    'Public Omega registry refutation; eventual-sign (n >> 0) statement.', 'none', ['outputs/history-screen.json'], '')
put(361291, 'EXCLUDED_ILL_POSED_ASYMPTOTIC',
    'arXiv:2312.16138v2 abstract; earlier lane r89 read Section 5 (Theorem 5.1, Claims 5.1/5.2).',
    'Modified Gregory bound 1/2 - O(k^5/n^3) is an unquantified asymptotic O-term proposed after the source disproves Gregory\'s original conjecture; no finite certificate possible.', 'none', ['sources/2312.16138-abs.html'], '')
put(370134, 'PARKED_DEEP',
    'arXiv:2509.03150v1 Sections 2.2, 5 (Lemma 2.9, Conjecture 5.5 = [Garamvolgyi, Conjecture 6.4], Proposition 5.6) read; sibling 370133 parked by r222.',
    'Stress-linkedness is defined through all generic realisations; no finite kernel certificate available; no mechanism.', 'none', ['sources/2509.03150v1.html'], '')
put(371090, 'PARKED_FAMOUS', 'arXiv:2510.19411v1 abstract read.',
    'Archdeacon-Jaeger oriented 5-cycle double cover conjecture (famous, open); source only uses it as a hypothesis.', 'none', ['sources/2510.19411-abs.html'], '')
put(353510, 'PARKED_DEEP', 'arXiv:2202.01852v4 abstract read.',
    'Dimension-free Picard-rank bound for toric Fano varieties at fixed codegree; deep algebraic geometry, no finite certificate.', 'none', ['sources/2202.01852-abs.html'], '')
assert len(R) == 20 and set(R) == {k for k in ex if not k.startswith('_')}, sorted(set(R) ^ {k for k in ex if not k.startswith('_')})
out = {}
for i in sorted(R, key=int):
    e = ex[i]
    out[i] = {'mathdb_id': int(i), 'title': e['title'], 'source_url': e['source_url'], 'provenance': e['provenance'],
              'raw_file': f'raw/{i}.jsonl', 'raw_file_sha256': H(f'raw/{i}.jsonl'), **R[i],
              'campaign_credit': 0, 'self_accepted': False}
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
arts = {}
for p in sorted(D.rglob('*')):
    if p.is_file() and p.name not in ('artifact-hashes.json',):
        arts[str(p.relative_to(D))] = hashlib.sha256(p.read_bytes()).hexdigest()
(D / 'artifact-hashes.json').write_text(json.dumps(arts, indent=1) + '\n')
print('results entries', len(out), 'artifacts hashed', len(arts))
for i, o in out.items(): print(i, o['outcome'])
