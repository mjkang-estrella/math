"""Root documentary verification and exact-public-result adjudication/routing."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'qtransversal-directsum-source-review-sol-r1'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def save(q,v):
 assert not q.exists(),str(q)
 q.write_text(json.dumps(v,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert json.loads((P/'ledger.json').read_text())['accepted_new']==57
ready0=json.loads((ROOT/'qtransversal-review-r1-ready.json').read_text());assert sha(A/'TASK.txt')==ready0['task_sha256']
m=json.loads((A/'SHA256-MANIFEST.json').read_text());entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])==145
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
exclusions=m['terminal_exclusions'];assert set(exclusions)=={'SHA256-MANIFEST.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
assert {str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()}==set(entries)|set(exclusions)
frozen=json.loads((A/'frozen-inputs.json').read_text());assert len(frozen)==26 and all(Path(n).is_relative_to(A) and sha(Path(n))==h for n,h in frozen.items())
after=json.loads((A/'frozen-after.json').read_text());assert after['count']==26 and after['mismatches']==[]
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=json.loads(q.read_text());assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert json.loads((A/'terminal_manifest.receipt.json').read_text())['exit']==0
budget=json.loads((A/'search-budget.json').read_text());assert budget==dict(calls_used=1,queries_used=3,maximum_calls=2,maximum_queries=6,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==1
c=charges[0];assert c['sequence']==1 and c['before']==dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True) and c['after']==budget
assert sha(A/c['plan'])==c['plan_sha256'] and json.loads((A/c['plan']).read_text())['queries']==c['queries'] and len(c['queries'])==3
assert isinstance(json.loads((A/'responses/search1.json').read_text()),str) and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[json.loads(s) for s in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=5,success=5)
for e in events:
 if e['event']=='success':assert sha(A/e['destination'])==e['sha256'] and (A/e['destination']).stat().st_size==e['bytes']
keyed=json.loads((A/'review.json').read_text());assert set(keyed)=={'373611'};g=keyed['373611'];assert g['accepted_credit']==0 and not g['qualified_survivor'] and g['prior_gate']=='EXACT_PUBLIC_PROOF_AUTHENTICATED_THEOREM2_JULY2026'
assert sha(A/'sources/rozhon-zamecnik.pdf')==g['public_counterpart']['pdf_sha256']=='2867bb077e2206908b6393bc9119ff83f3e090ebf47ff85e6016b89a1e18c7ac'
assert not json.loads((A/'SOURCE-ACCESS-INVENTORY.json').read_text())['new_denials']
record=dict(utc=now,mathdb_id=373611,source_lane=str(A),task_genesis_verified=True,manifest_sha256=sha(A/'SHA256-MANIFEST.json'),review_sha256=sha(A/'REVIEW.md'),proof_sha256=sha(A/'PROOF.md'),verified_manifest_files=145,verified_frozen_bindings=26,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,
 root_disposition='EXCLUDE_EXACT_PUBLIC_THEOREM_AND_COMPLETE_ROUTINE_BRIDGE',
 ordinary='Independent full ordinary PASS for exact finite-field arbitrary-given-presentation padded directsum,every mixedsubspace,universalbasis/Hall/rankenvelopebridges,empty/repeated/wholeambient/zero cases. Two derivations one result,not two reviews. Root records the independently reviewed proof,no new root mathematics or formalexecution.',
 public_counterpart=g['public_counterpart'],
 prior='Downloaded actual Characteristic-Compatible Lifting and Natural Direct-Sum Presentations for q-Matroids Theorem2p3,equation5,fullSection4p9 and relevantLemmas14-16pp7-8 expresslyresolveFulcherConj4.8 for actualgivenfamilies withoutcoordinate/minimalityassumption. Root personally read actual theorem and proof passage as documentaryadjudication; fullrelevantdependencycheck investigatorperformed. Currenthostasserts17July2026v1,pdfdatedJuly2026,pre-campaign chronology assertedbyhost/internaldate,no independent archival timestamp authentication. HostattributesVaclavRozhon/AdrianZamecnik,PDFauthorsBolzanoteam,distinctionpreserved;notpeerreview/legalidentitycertification.',
 significance='Root adopts zero-credit exactpublicresult exclusion. Independently also complete actualSaaltinkrank-envelope-to-source-directsum quotientcodimension application supports routine-adaptation exclusion,not shortness or familiar terminology. Strongest contrarycase actualMarch2026explicitnoncoordinateconjecture paidbutdoesnot overcome exactpublic theorem. No claim Saaltink2025printedexact directsum statement.',
 source='ActualFulcherNotation4.3defines exactpaddedlist forarbitrarypresentations,Conj4.8matches. Currentarxivabstracts forFulcher2603.13550/Saaltink2503.12201 listonlyv1/nojournalreferenceincopiedmetadata,boundednotworldwidefinalabsence. Universalbasisdefinition retained,Definition14dimensionphrasecomparedactualproof/Fulcherdefinition;no correctioncredit. trureturingrepresentabilitydifferentendpoint notclaimedmatchingdirectsumproof orunreadmatchingHOLD.',
 family='Bounded57+39scopesnonoverlap;allcoordinate/mixed/zero/repeated/finite-sumvariants ONEfamily,knownproof/helper/formalizationcredit0.',
 process='FiveGETtransport200(onePDF,fourHTML:authorpage,paperpage,twoarxivmetadata),oneprechargedsearchthreequeries,fullactualresponse. No newdenial/retry/rootmetadatareconstruction. Image-returntruncation/PNGdisplayfailure recoveredwithseparateimages/JPEG,originalreceiptsretained. Owninputs/products/PDFskillonly,nohistorical/protectedfilefollowreported. Actualsamplesonly,native/transient/writer/supervisorpeaksunknown,nouniversalcomplianceclaim.',
 root_scope='Documentary integrity and scientific acceptance/routing adjudication only,no root mathematical solving/programs/Lean/checkers.',keyed_review=keyed,credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=exclusions)
save(P/'qtransversal-directsum-source-parent-integration-sol-r1.json',record)
den=json.loads((ROOT/'inherited-denials-r480.json').read_text());den['utc']=now
delta='Completed373611independentordinaryPASS arbitrarygivenpresentations/allmixedsubspaces,ROOTEXCLUDEexactpublicresult0. ActualdownloadedDiderot Characteristic-Compatible Lifting and Natural Direct-Sum Presentations for q-Matroids Theorem2p3/fullSection4p9/relevantLemmas14-16pp7-8 provesexactFulcherConj4.8 withsamepaddedfamily,nocoordinate/minimalityassumption. Hostprojectdiderotpaper953fb228-9d1d-4038-9ff5-05d3af9a2a50asserts17July2026v1;PDFinternallyJuly2026/Bolzanoteam versushostRozhonZamecnik authors preserved,noindependentarchivaltimestamp/legalidentity/peerreviewclaim. Readactualmatchingproof,notexcerptorlabel. SeparatecompleteSaaltinkrank-envelope-to-targetquotientcodimensionbridge supportsroutineadaptationexclusion,notshortness;strongestMarch2026explicitconjecturecontrarycase retained. Noformaldispatch/recount.145ownfiles26frozen5GETsuccess(onePDFfourHTML),1search3queriesverified,nonewdenials. Fulcher/Saaltinkcurrentmetadataonlyv1,boundednotworldwidefinalabsence.57/60unchanged.'
den['root_qtransversal373611_scope']=delta;denpath=ROOT/'inherited-denials-r481.json';save(denpath,den)
config=json.loads((ROOT/'r477-config.json').read_text());config.update(number=478,protected_peers=['expanded-corpus-r476','expanded-corpus-r477'],peer_routing_files=['selection-routing-r476.json','selection-routing-r477.json'],denials=str(denpath),steering=config['steering']+'\n'+delta+'\n',year_floor=2000,candidate_pool=400)
config['excluded_ids']=sorted(set(config['excluded_ids'])|{373611});config['excluded_sources']=sorted(set(config['excluded_sources'])|{'https://arxiv.org/abs/2603.13550','https://arxiv.org/abs/2503.12201'})
save(ROOT/'r478-config.json',config)
spec=importlib.util.spec_from_file_location('root_discovery_packet',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=json.loads((Path(ready['lane'])/'historical-results-allowlist.json').read_text());forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
assert all(not any(t in part.lower() for t in forbidden) for n in allow for part in Path(n).relative_to(P).parts)
assert all(not any(f'expanded-corpus-r{n}' in x for n in [395,463,466]) for x in allow)
save(ROOT/'qtransversal-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r478',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=145,frozen_bindings=26,receipt_exit_counts=record['receipt_exit_counts'],disposition=record['root_disposition'],ready=ready)))
