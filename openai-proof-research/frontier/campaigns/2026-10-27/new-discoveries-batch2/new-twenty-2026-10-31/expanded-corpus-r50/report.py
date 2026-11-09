import pathlib,json,hashlib,datetime,subprocess
p=pathlib.Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();data=json.load(open(p/'extracted.json'));hist=json.load(open(p/'history-matches.json'));res={}
# Source depth denotes passages actually examined, never whole-paper clearance.
notes={
356298:'Nilpotent-radical cardinality divisibility might constrain group order from graph size; no primary body or concrete pair recovered. Need exact structure of isolated vertices and full counterexample or all-groups proof.',
356345:'Known: primary Theorem1.2(1) states exact all-m formula; proof pp10-11 uses symbolic unsatisfiability and Lemma4.5. No new proof credit.',
356361:'Bounded index power subgroup/translation VC asymptotics needs r restrictions and limiting field family. r=1 endpoint is a scope correction, not credited. Primary definitions unread.',
356391:'Need uniform asymptotic group family and exact matching definition; no full-scope slice-rank comparison. Primary body unread.',
356399:'Strong coloring forces induced matching color classes, but degree counting alone does not select rainbow Hamilton cycle. Primary body unread; no graph witness.',
356404:'General bipartite strong chromatic index bound has no tractable finite obstruction identified. Historical source-sibling notes retained; primary survey not read anew.',
356406:'Universal additive constant requires an infinite family or uniform bound. A single finite graph cannot refute the literal existential-C quantifier. Primary body unread.',
356407:'Delta=1 literal endpoint is a familiar domain correction and not an eligible discovery. No primary body read, no full intended-scope solution.',
356410:'Source Theorems4.1/4.3 and both proofs resolve the intended dimension5 cases via simplex concatenation and residual even-code Griesmer bounds. Literal general-k paraphrase is not the source scope; reject general-k widening.',
356417:'Bounding4-manifold and allowable handle conventions need source recovery. No topological proof or feasible literal Lean construction obtained.',
356464:'Known: Theorem1.4 stronger universal structural assertion implies existential minimum; proof of Theorem3.6 and final deduction inspected selectively. No new result.',
356491:'History has sibling356490 strategy-definition hold, not an exact exclusion of356491. Need multiplication table, loop action and winning-strategy convention before a finite automaton proof. No source body read anew.',
356538:'Source Definitions1-2 distinguish edge-size spectra P from vertex-size spectra pi. Literal count of all bipartitions is not the source invariant. A tree-count objection would attack the paraphrase; source fidelity parked.',
356543:'Known exact theorem: Selig-Zhu Theorem4.23 and proof, with cnat/Tutte bridge Theorem2.13 and edge-addition Lemma2.7 explicitly referenced. Decreasing permutation uniquely attains factorial. No new result.',
356634:'Embedding upper bound needs actual obstruction classes and parameter beta restrictions. Primary body unread; not replaceable by algebraic crossing check.',
356642:'Known refutation in source TheoremA, e.g. k=6,l=4 yields n=14<16. Main statement and introductory comparison inspected; full multisection proof not read. No new credit.',
356651:'Simplex-free uniform extremal theorem is substantial; need actual definition r-simplex and all parameter quantifiers. Source body unread; no candidate.',
356671:'Positive lower density among primes cannot follow from finite valuation computations. Need p-adic splitting/valuation conditions and Chebotarev-compatible characterization; primary unread.',
356708:'Current primary Conjecture4.1 assumes square of a bipartite graph and strong choosability; Theorem4.2 already obstructs an unrestricted extension. Paraphrase lacks restrictions, so no credit for exploiting the broader statement.',
356710:'Current primary Conjecture4.3 is 1-strong chromatic choosability. Ordinary list-colorability is weaker; Section4 and Theorem4.2 proof read, but no full threshold theorem or counterexample obtained.',
356711:'Literal low-chi ceiling conjecture not located in inspected current Section4. Need version-specific primary target; cannot silently replace with ordinary list bound or older paraphrase.',
356713:'Current Conjectures4.4-4.5 use m-strong choosability and distinct dependencies on m. Need exact avoiding-color quantifier/bridge; not established. Source scope hold.',
356732:'Bounded random/barbell search n8..24 found no exceeding edge derivative. Compared best lollipop for each n. This is neither proof nor exhaustive search; still need extremal inequality or explicit source-faithful graph.',
356733:'EXCLUDED_KNOWN_PUBLIC_REFUTATION. Independent exact11-vertex barbell computation: -24181/144<-3267/20, gap3293/720. Rational perturbation and independent hitting-time derivative certificates agree. Existing Omega AlbrightKemenyEdgeDerivativeRefutation.result refutes same claim at order23; definitions, spectral/grounded bridge portions and final endpoint read. Smaller witness is an uncredited parameter variant. No local Lean needed for known exclusion; upstream not replayed.',
356744:'Source Conjecture12 recovered; h>m negative formula is an endpoint/domain issue and uncredited. Intended restricted-sumset lower bound still requires full argument beyond known h2 case.',
356745:'Source Conjecture13 uses notation hA in restricted discussion and cites Karolyi h2; complement-h=m-1 degeneracy would only expose missing h restrictions. Need original intended inverse formulation; no substantive refutation.',
356746:'Source Conjecture14 recovered; endpoint/notation pitfalls retained. Need characterization at prime threshold, not just finite cyclic sample. No full proof.',
356747:'Source Theorem16/Conjecture17 recovered, including k,c,delta and known r2,h2 case. Need uniform strict comparison above threshold; no candidate.',
356799:'Twin-free/triangle-free equality characterization requires genuine maximality and all-n counting. Primary body unread; no constructive witness or lower-bound mechanism beyond generic branching.',
356830:'Primary Conjecture20 still states convex-polyomino queen minimum domination NP-completeness. Row/column convexity prevents arbitrary graph embedding; no faithful reduction.',
356833:'ROUTINE_REDUCTION: split4^d board into2^d side2 cubes, each a queen clique, giving upper2^d. Cartesian products of independent placements stay independent, so dimension2 four-queen placement plus dimension5 source-known32 placement give all d>=4 (even2a, odd5+2a). Recovered a32-point d5 witness by capped MILP and checked496 pairs exactly in Python. No novel mechanism beyond products and source base computations; no discovery nomination or Lean formalization.',
356836:'Literal text corrupted by repeated4 delimiters. Need source edge-colorability and multigraph conventions before any exact endpoint. Primary unread; no widening.',
356859:'Minimum degree oriented discrepancy assertion needs actual Hamilton orientation convention. Primary unread; no certificate.',
356874:'Known exact resolution: Bonamy-Botler-Dross-Naia-Skokan2023 Theorem2 gives19n strongly separating paths, hence weakly separating also. Definition, theorem and induction proof through5n-prime separating matchings read; remaining proof tail not audited. No new credit.',
356934:'Known source Theorem4.2 and full short proof: line graph K_n for even n has f_o=n(n-2)/4; n8 refutes bound12<14. No new credit.',
356984:'Rational negative-weight cycles and join conventions crucial; standard positive-weight shortest-cycle algorithm not full scope. Primary unread; no polynomial algorithm proof.',
357060:'Known exact current source Theorem5.10: polynomial exactly as requested. Proposition5.9 finite-field point-count proof and full theorem proof read (including b1 split/free lifts); no new result.',
357101:'No-infinite-path almost-sure statement requires full coupling/ergodic argument. Historical sibling source matches retained; no primary body read anew and no finite diagnostic promoted.',
357105:'Uniform additive constant in all planar degrees needs asymptotic coloring theorem. Primary body unread; no finite graph can alone refute existence of C.',
357114:'Current primary Conjecture1.4 matches broad equal-odd-hole question; raw references say refuted but primary passage read does not. Do not assert resolution from contradictory metadata. No full proof/counterexample; status remains unverified.'}
sources={356345:('myers','Theorem1.2 statement and pp10-11 proof'),356410:('codes','Theorems4.1/4.3, proofs and Lemma4.2'),356464:('weak-nkt','Theorem1.4, selected Theorem3.6 proof end and implication'),356538:('connected','Definitions1-2 and introduction'),356543:('cnat-selig','Theorem4.23 and complete short proof; target Chen-Ohlig5.3'),356642:('cycle-classes','Conjecture1.1/TheoremA and comparison; proof body not fully read'),356934:('odd-induced','Conjecture4.1/Theorem4.2 and complete short proof'),357060:('subrings','Proposition5.9 and Theorem5.10 proofs'),356874:('separating-proof','Theorem2 and proof beginning/matching construction'),357114:('odd-holes','Conjecture1.4 and adjacent Theorem1.3 scope')}
for i in [356708,356710,356711,356713]:sources[i]=('choosability','Section4 conjectures4.1-4.5 and Theorem4.2 proof')
for i in [356732,356733]:sources[i]=('kemeny','Section2 parameterization, Section3 spectral definition/Conjectures3.4-3.5')
for i in [356830,356833]:sources[i]=('queens','Attack definition, Section5 model/Table4/Conjecture26; Conjecture20')
for i in [356744,356745,356746,356747]:sources[i]=('additive','Section2 Conjectures12-14 and16-17, definitions and surrounding known cases')
receipts=sum([json.load(open(p/f)) for f in ['source-receipts.json','extra-source-receipts.json','further-source-receipts.json','registry-body-receipts.json']],[])
for si,x in data.items():
 i=int(si);r=x['record'];ss=sources.get(i);outcome='PARK_UNRESOLVED_PRIMARY_UNREAD'
 if ss:outcome='PARK_SOURCE_OR_PROOF_GAP'
 if i in [356345,356464,356543,356642,356874,356934,357060,356733]:outcome='EXCLUDED_KNOWN_RESOLUTION'
 if i==356410:outcome='EXCLUDED_KNOWN_INTENDED_DIMENSION5_SCOPE'
 if i==356833:outcome='EXCLUDED_ROUTINE_PRODUCT_OF_KNOWN_BASE_PLACEMENTS'
 files=list((p/'sources').glob(ss[0]+'.*')) if ss else []
 res[si]={'mathdb_id':i,'title':r['title'],'canonical_url':r['canonical_url'],'literal_statement':r['statement'],'statement_sha256':H(r['statement'].encode()),'raw_provenance':{k:v for k,v in x.items() if k!='record'},'source_url':r['source_url'],'outcome':outcome,'actual_review_depth':{'literal_statement_read':True,'primary_body_passages_read':ss[1] if ss else None,'entire_primary_body_read':False,'new_ordinary_math_attempt':i in [356732,356733,356833],'new_Lean_endpoint':False},'source_files':[{'path':str(f.relative_to(p)),'sha256':H(f.read_bytes())} for f in files],'inherited_matches':hist[si],'assessment_and_remaining_lemmas':notes[i],'novelty_cleared':False,'root_acceptance':False,'credit':0}
assert len(res)==40;assert set(map(int,res))==set(json.load(open(p/'reservation.json'))['ids']);(p/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False))
# Capture mutable ledger as selected administrative context, without copying history trees.
ctx={}
for q in [p.parent/'ledger.json',p.parent.parent/'ledger.json',p.parent.parent/'prior-campaign-context.json']:
 d=json.load(open(q));ctx[str(q)]={'sha256_at_read':H(q.read_bytes()),'accepted':d.get('accepted'),'exclusions':{k:v for k,v in d.items() if any(t in k.lower() for t in ['reject','exclude','held','protected'])}}
(p/'inherited-ledger-context.json').write_text(json.dumps(ctx,indent=2))
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean');ml=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');env={'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'lean_binary_sha256':H(lean.read_bytes()),'mathlib_expected_pin_from_assignment':'d13f23b723b8a846827a245b89c10fc7d3f11612','formal_manifest_sha256':H((ml/'lake-manifest.json').read_bytes()),'local_endpoint':False,'cache_trust':'Read-only provided cache, no upstream rebuild or transitive axiom audit claimed; no proof packet created.'};(p/'environment.json').write_text(json.dumps(env,indent=2))
print('exactly40 results; primary passage reads',len(sources));print('outcomes', {v:sum(x['outcome']==v for x in res.values()) for v in set(x['outcome'] for x in res.values())})
