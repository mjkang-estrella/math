from pathlib import Path
import hashlib,json,datetime,re
R=Path(__file__).resolve().parents[1];L=R.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,o):(R/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
records=json.loads((R/'records.json').read_text());notes={}
for line in (R/'work/notes.txt').read_text().splitlines():
 n,s,r=line.split('|',2);notes[int(n)]=(s,r)
assert len(notes)==50 and set(notes)=={x['mathdb_id'] for x in records}
primary={399608:['splines-report.txt:2290-2420','splines-successor.txt:1-158'],400254:['triangular-report.txt:2088-2177'],400883:['roots-report.txt:2586-2672'],403679:['tight-report.txt:950-1042'],403693:['tight-report.txt:2948-2982'],404584:['cube.txt:entire two pages'],404757:['schedule.txt:322-360,539-592,3380-3420'],405029:['modules-report.txt:530-654'],405091:['forest-report.txt:3145-3196']}
# Exact identifier matches in accepted/exclusion/history, plus explicit family-scope inspection.
history=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;b=p.read_bytes();obj=json.loads(b)
 hits=[x['mathdb_id'] for x in records if re.search(r'(?<![0-9])'+str(x['mathdb_id'])+r'(?![0-9])',b.decode())]
 history.append({'path':str(p),'sha256':sha(b),'exact_id_hits':hits,'scope':'All fifty compared by exact identifier; distinct titles/source targets compared with accepted-family list. No positive clearance of live literature inferred.'})
print('history exact identifier matches',history)
rows=[]
for x in records:
 n=x['mathdb_id'];status,reason=notes[n]
 rows.append(dict(mathdb_id=n,title=x['title'],canonical_url=x['canonical_url'],literal_statement=x['statement'],literal_sha256=sha(x['statement'].encode()),literal_bytes=len(x['statement'].encode()),source_url=x.get('source_url'),disposition=status,reason=reason,quantifier_and_scope_review=reason,evidence_level='retained-primary-body' if n in primary else 'literal-statement-only',literal_review=True,primary_body_review=n in primary,primary_locations=primary.get(n,[]),concluding_proof_section_read=n==404584,complete_dependencies_read=False,bounded_novelty_cleared=False,accepted_credit=0,proposal=False))
put('dispositions.json',{'schema_version':1,'dispositions':rows,'count':50})
put('proposals.json',[])
put('history-scope-screen.json',{'matches':history,'cayley_exclusion':{'id':364119,'path':str(L/'root-mathdb-cayley-review-intake-r363/disposition.json'),'action':'Source examples and successor applicability precede any calculation. No source adaptation is offered as discovery.'},'limitations':'No current registry head clearance: no significant discovery investment or acceptance proposed. Cached history is an administrative screen, not live priority proof.'})
put('bounded-checks.json',{'calculations':[],'reason':'Source/example/subsumption checks killed cheap routes before calculation. No finite sweep, symbolic search or numerical novelty claim. Hash/set integrity checks are administrative and not mathematical evidence.','primary_body_records':sorted(primary),'proof_section_records':[404584],'complete_dependency_reviews':0,'proposals':0,'resource_caps':{'AS_bytes':536870912,'sampled_process_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'guard':str(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1','python':'python3 -B'},'observed_peak_group_RSS_bytes':131260416,'observed_max_helper_wall_seconds_before_final':6.067570222076029})
put('source-versions.json',[{'url':e['url'],'version':e.get('version'),'utc':e['utc'],'sha256':e.get('sha256'),'size':e.get('size'),'usable':e['usable']} for e in json.loads((R/'source-provenance.json').read_text())])
(R/'failures.md').write_text('Wiley https://onlinelibrary.wiley.com/doi/10.1002/jgt.23244 returned HTTP 403. Stopped; no retry or TLS workaround. Error retained in source-provenance.json; no response body was available for reading. The original OWR report independently says the clique conjecture was proved. No challenge detected in retained successful responses.\n\nNo MathDB requests (429HOLD), browser/account work, Google requests, GitHub API/raw/codeload/diff, ScienceDirect fetch, public mutation, external message, Lean or manuscript work. Search service returned some forbidden-host search snippets; those hosts were never opened and those snippets are not used as evidence.\n\nNo eligible proposal survived. The forty-one literal-only rows have no primary-body clearance. No claim of global novelty or current exact open status is made. Splines successor is unrefereed; its claim is a material collision, not independently validated acceptance. Scheduling successor assumes SPD Jacobian; arbitrary-T literal scope is not certified solved.\n')
# Retain exact excerpts already read, not recursive corpus/history copies.
excerpts=[]
for name,a,b in [('cube',1,200),('roots-report',2586,2672),('splines-report',2290,2420),('splines-successor',1,158),('tight-report',950,1042),('tight-report',2948,2982),('triangular-report',2088,2177),('modules-report',530,654),('forest-report',3145,3196),('schedule',322,360),('schedule',539,592)]:
 p=R/'work'/(name+'.txt');lines=p.read_text().splitlines();excerpts.append(f'FILE work/{name}.txt LINES {a}-{b}\n'+'\n'.join(lines[a-1:b]))
(R/'primary-excerpts.txt').write_text('\n\n'.join(excerpts)+'\n')
(R/'SUMMARY.md').write_text('''# r374 qualified breadth handback

Reviewed exactly the fifty reserved r373 literal statements; individual statements, UTF-8 SHA256, scope objections and evidence levels are in dispositions.json. Zero proposals; zero discovery credit. Nine retained primary-body record reviews, one concluding old proof section read (Barber), zero complete dependency audits or novelty clearances. Forty-one rows are literal review only. No manufactured survivor.

The exact fifty match queue.json, are disjoint from r359 and r371 active reservations, and have no overlap with the bound 833-record coverage. Twenty r301 corpus chunks verified in place against inventory. Root r373 manifest and original references, r304 accepted/exclusion/history, and r363 Cayley exclusion are bound without copying those trees. Freeze preceded corpus statement extraction. Sources were retained with URL/version/UTC/hash before extraction and review. Source PDFs were mechanically converted for reading; that alone is not body review.

Decisive source findings: 403679 is refuted in its own source (Huang–Ma; Janzer). 403693 is explicitly reported proved immediately after its source conjecture. 404584 is Barber’s old full odd/even formula with four residue-class constructions. 399608 has a retained September 2026 exact-formula preprint collision (unrefereed; no proof certification claimed). 404757 has a direct 2025 primary successor under SPD hypotheses; no all-map assertion. 400254 has a source proof for sufficiently large n, leaving the literal every-n scope unclaimed. 400883 symmetric subclass is already handled by source Theorem 4, with no cheap nonsymmetric route. 405029 source specifies finite support, excluding all-functions evasions. 405091 asks for useful combinatorics beyond its already-known positivity/multiplicity-free result; routine basis inversion earns no credit.

No decisive calculation was warranted after source checks. No hard sweep or discovery/formal/manuscript investment. No theorem or complete new ordinary proof was found to route for independent review. Bounded prior checks justify parking leads, not worldwide priority or exact current status claims. Search failures/access limits and evidence gaps are retained. No current public registry head clearance is claimed because no significant new candidate investment or acceptance is proposed.

Counts stay 9 additional / 39 total / next 40. Root alone reconciles latest coverage; this lane does not update the ledger or claim coverage integration. MathDB requests: zero. All helpers ran under the fixed helper_guard.py caps and required environment. No reservation/shared/index/git changes.

Run verify.py under the same guard. manifest.json lists SHA256 and sizes of every delivered file except itself and verification-receipt.json. The receipt is generated by a separate final invocation and checks originals, corpus, exact sets, literal hashes and full manifest membership, failing nonzero on any mismatch.
''')
put('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scientific_input_bindings':'input-bindings.json','freeze':'freeze-receipt.json','retrievals':'source-provenance.json','versions':'source-versions.json','searches':['search-results.json','search-successors.json'],'literal_hash_encoding':'SHA256 exact UTF-8 statement string, no normalization','prohibited_requests':0,'external_messages':0,'counts_unchanged':[9,39,40],'new_result_proposals':0})
