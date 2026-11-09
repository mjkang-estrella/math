import json, pathlib
D = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((D/'extracted.json').read_text())
R = {
 '342735': dict(review_depth='primary body read (v1,v2,v3 conjecture text identical; Thm 3.x upper inclusion, Prop qk_admissible, Prop fibonacci_counter_example); live Omega registry file read',
   outcome='excluded_known_registry_resolution', detail='Peltomaki silver-slope abelian-period conjecture is formalized and marked proved in the Omega registry: Blueprint/D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.md and D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.lean at HEAD bbd7a670 (fetched 2026-11-03; sha256 in sources/registries/omega-silver). Also present in root complete tree b576c901. Route stopped.'),
 '342741': dict(review_depth='primary body read (conjecture in 1905.06926v1 sec. 2); later paper abstract read',
   outcome='excluded_published_resolution', detail='Proved by Antolin Camarena and Carnero Bravo, arXiv:2307.12401 (v1,v2), which computes Ind(K2 x Km x Kn) and proves the Goyal-Shukla-Singh conjecture.'),
 '342757': dict(review_depth='primary body read (Laugesen 1905.07658v1 Conjecture gapmonotpure); refuting paper abstract read',
   outcome='excluded_published_resolution', detail='Disproved by Dai and Sun, arXiv:2609.23544 (2026-09-20): the ratio is strictly increasing on suitable polyhedral domains on any compact positive interval; they also prove the box case.'),
 '342782': dict(review_depth='statement and source abstract (Deift-Miller-Trogdon 1905.08408v1) screened; no finite mechanism',
   outcome='parked_analytic_probabilistic', detail='Universality of a limiting law for normalized stopping times; the class of distributions mu is not sharply specified in the MathDB paraphrase. No finitely checkable route; parked.'),
 '342972': dict(review_depth='primary body read (Kardos-Narboni 1906.05638v1 Conjecture conj:weak and Theorem th:conj_equiv)',
   outcome='excluded_source_settled', detail='The weak signed edge-labeling existence claim is the source Conjecture 2. The same paper proves it equivalent to the Macajova-Raspaud-Skoviera signed 4-colour conjecture and gives a counterexample to that conjecture, so the claim is false by the source itself (zero-credit source-settled).'),
 '342976': dict(review_depth='primary statement read (Kwon-Oum 1906.05753 v1/v2); resolving paper abstract read',
   outcome='excluded_published_resolution', detail='Proved by Kwon, McCarty, Oum and Wollan, arXiv:1911.00230 (JCTB 149 (2021) 76-91): large rank-depth iff long path vertex-minor.'),
 '343124': dict(review_depth='primary statement read (1907.00853v1 Conjecture conj:BJTh); literature search',
   outcome='parked_famous_open', detail='Bang-Jensen-Thomasse supereulerian conjecture: famous, open even for alpha=2 per source; no disproof found. No exhaustive digraph search run (labelled digraphs on >=6 vertices exceed the lane caps); parked.'),
 '343210': dict(review_depth='primary statement read (Magsino-Mixon-Parshall 1907.05971v1 conj:wewin); literature search',
   outcome='parked_infinitary', detail='Asks for infinitely many primes with LS(p) < floor(HP(p)); finite computation cannot settle it and no uniform dual-certificate mechanism was found in this pass. Parked.'),
 '343244': dict(review_depth='v1 and v4 e-prints read',
   outcome='excluded_source_version_withdrawn_and_famous', detail='The integral four-square optimal strong approximation conjecture appears in 1907.07839v1 but is commented out in v4 (replaced by a function-field conjecture conjectured4); it is also a famous hard conjecture (Sardari). Treated as withdrawn from this source; parked/excluded.'),
 '343471': dict(review_depth='primary body read (Gao-Gu 1908.03914 Conj. conj:Morse3adic); exhaustive 3-adic alpha-tree test',
   outcome='parked_consistent_computation', detail='Computed L_n mod 3^40 for n<=2200 (weighted Catalan, b(h)=(2h+1)^2). The digit tree of admissible alpha stays alive: alpha = 116 mod 3^5 forced, 27 residues mod 3^8 alive (logs/morse-2.log). No counterexample; no proof mechanism. Parked.'),
 '343472': dict(review_depth='primary statement read (Bloom-McNew 1908.03953 v1/v2 identical)',
   outcome='parked_open', detail='Source proves non-algebraicity only when the two largest parts differ by 1 (Cor. not rational); the general case needs transcendence arguments; parked.'),
 '343489': dict(review_depth='primary statement read (Pelekis-Vlasak 1908.04727v1); resolving note abstract read',
   outcome='excluded_published_resolution', detail='Proved by Janzer, arXiv:1911.03421 (2019-11-08): antichains in [0,1]^n of (n-1)-dimensional Hausdorff measure n exist for every n.'),
 '343506': dict(review_depth='primary statement read (Amarra-Morgan-Praeger 1908.05128v1); resolving paper abstracts read',
   outcome='excluded_published_resolution', detail='Marsh, arXiv:2608.12526: H_{k,n} = Sh(C_k,n) is 2-transitive when n is not a power of k and is Alt or Sym(kn) except C_k wr C_{f+1} (n=k^f) and AGL cases for k=4; proves the cyclic conjecture. (Xia-Zhang-Zhang-Zhu 2304.01037 concerns the full shuffle group.)'),
 '343628': dict(review_depth='primary body read (Bujtas-Irsic-Klavzar 1908.09513v1 and author-site revision 2020-01-08, Conjecture 5.4/6.1); exhaustive search beyond source range',
   outcome='parked_verified_beyond_source_range', detail='Exhaustive twin-aware search reproduces the source Table exactly (perfect graphs 4,11,32,122,536,2754,15752; connected 2,6,19,81,386,2102,12476; minimally imperfect 0,0,2,8,1,1,1 for n=3..9) and extends: 98319 gamma_g-perfect graphs on 10 vertices; minimally gamma_g-imperfect graphs on 10 and 11 vertices are only the antiholes. Complement reformulation (minimal induced members of {no false twins, min degree >=2, orthogonal pair}) recorded; no full proof. Parked.'),
 '343646': dict(review_depth='primary statement read (Bilyk et al. 1908.10354v1 conj1)',
   outcome='parked_analytic', detail='Discreteness of p-frame energy minimizers for non-even p; analytic, open; source proves only empty interior of the support. Parked.'),
 '343796': dict(review_depth='primary statement read (Galashin-Postnikov-Williams 1909.05435v1, sec. on higher associahedra)',
   outcome='parked_heavy_polyhedral_computation', detail='Generic convex n-gon f-vector invariance; verifying beyond n=7 needs exact fiber-polytope/convex-hull computations not feasible under the python-only cap; parked.'),
 '344002': dict(review_depth='primary body read (Graham 1910.00924v1 Def 1.1, Thm 2.2, equivalence section, Conjecture conjexceptionalZprime); exact certificate; weighing-matrix literature partly read',
   outcome='candidate_counterexample_prior_art_risk', detail='Two (indeed three) affinely inequivalent 25-element extreme subsets of Z_71, supports of +-1 sequences with autocorrelation 25*delta (CW(71,25)). Exact proof in proof-344002.md; uncompiled Lean draft lean-draft-344002/. MATERIAL RISK: Strassler 1998 (JSPI 73) printed four inequivalent CW(71,25) (body unread, ScienceDirect not accessed); if their supports are inequivalent the contradicting objects were published, the 355525 pattern.'),
 '344003': dict(review_depth='primary statement read (Graham Conjecture conjDiffPS)',
   outcome='parked_no_certifiable_mechanism', detail='A counterexample needs two inequivalent non-extreme sets with provably equal Sidon constants; exact Sidon constants are non-convex optimization values and no structural equality mechanism was found. Parked.'),
 '344004': dict(review_depth='primary statement read (Graham Conjecture conjprimecards)',
   outcome='excluded_not_well_posed', detail='Qualitative frequency claim ("appear more frequently") without a defined measure; not a precise mathematical statement.'),
 '344302': dict(review_depth='primary body read (Zhu 1910.12818 v1/v2 Conj 6.2); Hanni 2011.14360 partial result read; full ordinary proof',
   outcome='candidate_full_proof_ordinary_no_lean', detail='Proof for all n: exact convolution identity, meromorphic generating function 1/f with real poles x0(1+3k), interval-certified error bounds for n>200, exact DP for 4<=n<=200. See proof-344302.md and outputs/dd-rigorous-output.txt. Lean not attempted (needs Cauchy estimates and certified transcendental bounds).'),
}
out = {}
for k in sorted(ex):
    e = ex[k]; r = R[k]
    out[k] = {'mathdb_id': int(k), 'title': e['title'], 'source_url': e['source_url'],
              'provenance': e['provenance'], 'review_depth': r['review_depth'], 'outcome': r['outcome'],
              'detail': r['detail'], 'self_accepted': False}
assert len(out) == 20
(D/'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(out))
