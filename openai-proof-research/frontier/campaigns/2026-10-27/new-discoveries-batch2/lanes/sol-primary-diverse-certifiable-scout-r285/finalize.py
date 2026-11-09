from research import *
admin=json.loads((L/'administrative-snapshot.json').read_text())
ledger=json.loads((L/admin[2]['snapshot']).read_text());prior=json.loads((L/admin[3]['snapshot']).read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
prov=dict(status='partial scout; no eligible resolution',time=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),counts_snapshot=[9,39,40],count_authority='root alone; no changes',scientific_bindings='bindings.jsonl',immutable_registry_originals='duplicate-filter-bindings.json',administrative_snapshots='administrative-snapshot.json',primary_versions={k:'https://arxiv.org/pdf/'+v+'v1' for k,v in [('cycles','2411.10046'),('coxeter','2410.09897'),('fullerenes','2410.19322'),('polynomials','2312.07754'),('reliability','2405.11510'),('codes','2312.09482'),('caro-tuza','2408.04257'),('dualcritical','1410.1653'),('rainbow-successor','2609.11437')]},chronology=['Linton model 1976 and Horak–Rosa question 2005 are attributions in later frozen primary sources; original bodies not acquired','Dual-criticality primary v1: October 2014','Polynomial problems presented July 2023, v1 December 2023','Caro–Tuza August 2024; workshop September 2024, v1 November 2024','Rainbow partial successor September 2026; not a full solution of workshop 4.1'],limitations=['No worldwide novelty or current-openness claim','Current GitHub registry head unavailable under inherited denied-route constraint; no retries','No MathSciNet or zbMATH completeness claim','No new browser, external messages, shared files, git, Lean or manuscript changes','Historical era breadth is weaker than author/topic breadth; old original sources not silently certified','No full proof-body sweep for every held family; only target and identified exclusions receive detailed bodies'],caps=dict(AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230,cap_raises=False),guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(L/'provenance.json').write_text(json.dumps(prov,indent=2))
(L/'failures.json').write_text(json.dumps([
dict(stage='navigation parser',error="ModuleNotFoundError: No module named bs4",exit=1,resolution='Used standard-library regex; no dependency install'),
dict(stage='historical search form',error='1990 rejected by arXiv as invalid publication year; HTTP 200 form response',preserved=['primary/old-problems.html','primary/old-conjectures.html'],resolution='Corrected date lower bound to 1991; no access control encountered'),
dict(stage='report generation',error='RuntimeError: When g(x) and f(x) are non-constants',exit=1,resolution='Source line wraps normalized via original Linton paragraph locator'),
dict(stage='mechanism 1',error='Greedy deletion not confluent',certificate='exact-checks.json'),
dict(stage='mechanism 2 shortcut',error='Type A does not imply dual-criticality of same graph',certificate='exact-checks.json')],indent=2))
(L/'SUMMARY.md').write_text('''# r285 handback

No full eligible resolution. Fifteen distinct source-question families scoped across graph theory, Coxeter groups, approximation, potential theory, spectra and reliability. One provisional solving survivor: Caro–Tuza Type A/Type B parity-order recognition. Counts snapshot stays 9 additional / 39 total / next 40; root alone decides/counts.

Main concrete progress: exact independent-source-set reduction to dual-criticality; certified failure of arbitrary greedy deletion; certified separation of Type A from dual-criticality on the same graph. An independent permutation verifier and subset DP agree on all 1,099 labeled graphs through five vertices, including verification of the reduction. These are helpers, not resolution credit.

Nikolov's snake conjecture is excluded after inspecting the exact cached refutation body. The binary code intersection conjecture is already refuted by the inspected coding paper; it was dropped before the final 15-family list. The fullerene uniform-sampling existence question has its routine enumeration bridge in its own source. Other holds retain scope and history gaps. SCOUTING.md gives statements, exact source pages and dispositions; discovery.md gives mechanisms and residual gaps.

Limitations: most newly acquired problem-posing collections date to 2023–2024; older eras are largely historical attributions. Only the ranked route and identified exclusions received detailed closest-proof-body inspection. Live arXiv search/body checks were made, but no current public GitHub registry head was fetched because those routes are inherited as denied. No blanket novelty/current-openness claim.

Primary bytes are in primary/ with SHA-256 bindings; the large immutable registry is referenced by original path/hash, not copied. Administrative files are snapshots only. failures.json retains errors and rejected hypotheses. Verification is a separate guarded invocation after manifest creation. MANIFEST.json excludes itself and verification-receipt.json. No PROOF.md because there is no full endpoint.
''')
(L/'progress.md').write_text('''# Progress and replay

Read ancestor and batch instructions, ledger/prior-context snapshots and r282 disposition. Avoided reserved octahedron, focused Zeckendorf, canonical reduction, zero-sum, knight-tour, Swanepoel, harmonic-denominator and cumulative finite-field targets. Worked solo within assigned lane.

Fresh primary-first navigation produced six problem-posing/solving papers, followed by three targeted bodies: Caro–Tuza, Király–Kisfaludi-Bak, and the 2026 rainbow partial successor. Frozen source bytes and extracted text precede scientific reading. The cache was consulted after generating source candidates and used as a semantic exclusion filter. Its broad term hits are deliberately not treated as proof of scope matches. The exact snake proof body was inspected. No retrieval hit is taken as novelty clearance.

Two sustained mechanisms on parity ordering led to an exact reduction but no polynomial algorithm. The selected finite tests validate a structural reduction and certify shortcut failures; they are not an expanded census of hypothetical solutions. Exact remaining gaps are in discovery.md.

Replay from repository root, with the required environment variables OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1, through the assigned absolute helper_guard.py: run python <lane>/checks.py. It deterministically regenerates exact-checks.json. Then run python <lane>/verify.py separately to verify manifest and original scientific references; the latter writes only the excluded receipt. Never invoke scientific helpers outside the guard. Caps remain AS/groupRSS 512 MiB, CPU 210 s, wall 230 s. Checks completed in well under one second; registry filter completed in about 14 seconds. No caps raised.

Do not interpret the independent-source-set bridge as a full answer: its search is exponential, dual-criticality has a randomized fixed-parity method in the inspected 2014 source, and Type B has only an exponential verifier here. A future lane needs either a genuine source-set compression or a different target.
''')
# Final manifest is deliberately last; receipt is written by a separate process.
rows=[]
for p in sorted(L.rglob('*')):
 if not p.is_file() or p.name in ['MANIFEST.json','verification-receipt.json']:continue
 d=p.read_bytes();rows.append(dict(path=str(p.relative_to(L)),bytes=len(d),sha256=sha(d)))
(L/'MANIFEST.json').write_text(json.dumps(dict(files=rows,excludes=['MANIFEST.json','verification-receipt.json']),indent=2))
print('manifest files',len(rows),'counts',prov['counts_snapshot'])
