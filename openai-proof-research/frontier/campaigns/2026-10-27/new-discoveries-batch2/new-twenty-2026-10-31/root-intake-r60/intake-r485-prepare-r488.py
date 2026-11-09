"""Root-only documentary integrity/disposition/disjoint routing; no mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,collections,re,base64,importlib.util
P=Path(__file__).resolve().parent.parent;ROOT=P/'root-intake-r60';A=P/'expanded-corpus-r485'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dg(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def save(p,d):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
route=read(ROOT/'selection-routing-r485.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
m=read(A/'manifest.json');entries=m['files'];assert isinstance(entries,dict) and len(entries)==175
for n,v in entries.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts
 q=A/n;assert not q.is_symlink() and sha(q)==v['sha256'] and q.stat().st_size==v['bytes'],n
ex=m['terminal_noncircular_self_exclusions'];assert set(ex)=={'manifest.json','terminal_manifest.receipt.json','terminal_manifest.output.txt'}
actual=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():actual.add(str(q.relative_to(A)))
assert actual==set(entries)|set(ex)
frozen=read(A/'frozen-inputs.json');assert len(frozen)==13 and all(Path(n).parent==A and sha(Path(n))==h for n,h in frozen.items())
after=read(A/'frozen-after.json');before=read(A/'frozen-before.json');assert before['count']==after['count']==13 and before['mismatches']==after['mismatches']==[]
gates=read(A/'results.json');originals=read(A/'originals.json');prov=read(A/'original-provenance.json');ids=read(A/'reservation.json')['ids'];assert len(ids)==20 and set(ids)==set(map(int,gates))==set(map(int,originals))==set(map(int,prov))
chunks={};sources={}
for key,row in prov.items():
 q=Path(row['chunk']);assert q.is_relative_to(P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus')
 if str(q) not in chunks:
  b=q.read_bytes();chunks[str(q)]=(dg(b),b.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==row['chunk_sha256'];raw=lines[row['line']-1];obj=json.loads(raw)
 assert row['newline'] is True and raw.endswith(b'\n') and dg(raw)==row['raw_sha256'] and base64.b64decode(row['raw_base64'],validate=True)==raw and (A/'original-lines'/f'{key}.jsonl').read_bytes()==raw
 assert obj==originals[key] and obj['mathdb_id']==int(key)
 tokens=re.findall(rb'"statement"\s*:\s*("(?:[^"\\]|\\.)*")',raw);assert len(tokens)==1;token=tokens[0]
 assert token==base64.b64decode(row['statement_token_base64'],validate=True)==(A/'statement-tokens'/f'{key}.json').read_bytes() and dg(token)==row['statement_token_sha256'] and json.loads(token)==obj['statement']==gates[key]['literal_gate']['statement']
 assert dg(obj['statement'].encode())==row['decoded_sha256'] and (A/'statements'/f'{key}.txt').read_text()==obj['statement'];sources[key]=obj['source_url']
receipts=[]
for q in sorted(A.glob('*.receipt.json')):
 v=read(q);assert v['cwd']==str(A) and v['cpu_limit_s']==115 and v['as_limit_bytes']==6*1024**3 and v['deadline_s']==130 and len(v['affinity'])<=2 and v['group_rss_guard_bytes']==6*1024**3 and v['killed'] is None
 receipts.append(dict(path=q.name,sha256=sha(q),exit=v['exit']))
assert read(A/'terminal_manifest.receipt.json')['exit']==0
budget=read(A/'search-budget.json');assert budget==dict(calls_used=2,queries_used=6,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==2
prev=dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True)
for i,c in enumerate(charges,1):
 assert c['sequence']==i and c['before']==prev and sha(A/c['plan'])==c['plan_sha256'] and read(A/c['plan'])['queries']==c['queries']
 nxt=dict(prev,calls_used=i,queries_used=prev['queries_used']+len(c['queries']));assert c['after']==nxt;prev=nxt
 response=read(A/f'search-response-{i}.json');assert isinstance(response,str) and len(response)>1000
assert prev==budget and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
events=[];prev='0'*64;pdfs=0
plans={dg(json.dumps(read(q),sort_keys=True).encode()):read(q) for q in A.glob('plan-*.json')}
for i,line in enumerate((A/'guard-ledger.jsonl').read_bytes().splitlines(keepends=True)):
 e=json.loads(line);assert e['seq']==i and e['previous']==prev;prev=dg(line);events.append(e)
 if e['event']=='success':
  q=A/e['destination'];assert sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
  if q.read_bytes().startswith(b'%PDF'):pdfs+=1
 if e['event']=='attempt':assert e['plan_sha256'] in plans and '/server/api/' not in e['url'] and e['url'].startswith('https://')
counts=collections.Counter(e['event'] for e in events);assert counts==dict(attempt=8,success=7,redirect=1) and pdfs==5
payload=A/'sources/poly-final.html';assert payload.stat().st_size==2638 and b'Redirecting' in payload.read_bytes()
assert read(A/'get_poly_final.receipt.json')['exit']==0 and read(A/'new-unavailability.json')['arxiv']=='math/0601731'
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==808
forbidden=('formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite')
for x in history:
 rel=Path(x['path']).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(f'expanded-corpus-r{n}' in x['path'] for n in [395,463,466,482]) and x['path'] in allow and allow[x['path']]==x['sha256']
summary='379539authorordinaryunrestricted-v2/literalrefutation Phi=(y-x-1)(y-2x),singularcomponentZ[1/2],nonsingular2regularinfinitecomponents1/3versusi notisomorphic;actualauthorreportrequiresfiniteH,finite-Hwitnessunpaid,source/domain/significance/finalPARK,noindependentPASS/formaldispatch.320041actualCEDConj5.4matched,two-triangleexamplelacksCEDinputnotrefutation;relative rank-selectedembedded-earball/completionlemmaunpaid.379628actual0810.2247v1Th1.1/1.3Section4bothconditionspublicsolution0,positiveboundaryk=t-n-1repair0,deepSchuridentityattributednotfreshproofaudit.379541specificGakuLiu1606.05033bodyunreadHOLD;379601source-refutationreportnotauthenticatedRAAGwitness. Seventeenassignedoriginalbodiesunread.'
record=dict(utc=now,source_lane=str(A),task_reservation_genesis_verified=True,manifest_sha256=sha(A/'manifest.json'),verified_manifest_files=175,verified_original_bindings=sorted(ids),verified_frozen_bindings=13,source_url_by_id=sources,all20_gates=gates,runner_receipts=receipts,receipt_exit_counts=dict(collections.Counter(str(x['exit']) for x in receipts)),guard_events=dict(counts),search_budget=budget,root_disposition='ZERO_QUALIFIED_SURVIVORS_379539_SCOPE_PARK',scientific_summary=summary,reading_limits='Seventeenoriginalbodiesunread,novisualfigures. Actualv2unrestrictedsourceversusfiniteHauthorreport comparisonpaidbyworker; unreadfinalnotassumedequivalent. Noindependentreview/completepublicroutinebridgeforexactPhiwitness.',process='175ownfiles20raw/token/decodedcorpusbindings13frozen808savedhistorypathsverifiedwithoutrootfollowinghistoricalpaths.8chargedGET7payloads(5PDF,metadataHTML,redirectHTML),2search6querieslivecontinuity/fullresponsesverified. Search1firstpersistenceinvocationdidnotsave,responsepersistednextinvocationBEFOREfurtherresearch/acquisition;failure/deviationretained,nosearchretry/refund/reset,notflawlessimmediatepersistclaim. Sampledtelemetry/nativetransientwriterlimitsretained,nouniversalcomplianceclaim.',root_scope='Documentaryprovenance/integrity/routingonly,no root mathematical solving/programs/Lean/checkers.',credit=0,accepted_new=57,target_new=60,formal_dispatch=False,terminal_self_exclusions=ex)
delta='Completedr485zeroqualifiedsurvivors. '+summary+' NEW ENTIREBrunatMontes On polynomial digraphs DiscreteMath306(2006)401-412 DOI10.1016/j.disc.2006.01.001/PIIS0012365X06000021/originalmath0601731 ALLNEWdeliveryunavailable after2638byteRedirectingHTML;explicitpre-failurev2/reportonlynotfinalequivalence.175ownfiles20bindings13frozen808savedhistorypathsverified,8chargedGET7payloads1redirect2search6queries;firstsearchpersistenceomissionrepairednextinvocationbeforefurtherresearch,originalreceiptsretained. Noformaldispatch/credit,57/60unchanged.'
den=read(ROOT/'inherited-denials-r492.json');den['utc']=now
den['blocked_keys']=sorted(set(den['blocked_keys'])|{'doi.org/10.1016/j.disc.2006.01.001','linkinghub.elsevier.com/retrieve/pii/S0012365X06000021'})
den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{'math/0601731','0601731','10.1016/j.disc.2006.01.001','s0012365x06000021','on polynomial digraphs'})
den['records'].append(dict(url='https://doi.org/10.1016/j.disc.2006.01.001',reason=dict(status='DOI302linkinghub2002638byteRedirectingHTMLnotpaper',artifact='BrunatMontes On polynomial digraphs DiscreteMath306(2006)401-412/originalmath0601731',restriction='ENTIRE identified work ALL NEW hosts,versions,arxiv,authors,caches,mirrors,DOI/API,body/metadata deliveries unavailable. No retries/identity correction/indirect recovery. Explicitalready-supplied pre-failurev2/report only,notfinalequivalence. Distinctotherdigraphpapersnotblanketdenied.'),evidence=dict(path=str(A/'new-unavailability.json'),sha256=sha(A/'new-unavailability.json'),guard_sha256=sha(A/'guard-ledger.jsonl'),payload_sha256=sha(payload))))
den['root_r485_scope']=delta;denpath=ROOT/'inherited-denials-r493.json'
# All integrity checks precede root integrations and new packet construction.
save(P/'expanded-corpus-r485-parent-integration.json',record);save(denpath,den)
config=read(ROOT/'r487-config.json');config.update(number=488,protected_peers=['expanded-corpus-r487','split-decomposition-orthogonality-source-review-sol-r1'],peer_routing_files=['selection-routing-r487.json','selection-routing-split-orthogonality-review-r1.json'],denials=str(denpath),year_floor=2000,candidate_pool=400,quarantined_discovery_numbers=[395,463,466,482])
config['completed_discovery_numbers']=sorted(set(config['completed_discovery_numbers'])|{485,486})
config['excluded_ids']=sorted(set(config['excluded_ids'])|{379539,382572})
config['excluded_sources']=sorted(set(config['excluded_sources'])|{'https://arxiv.org/abs/math/0601731','https://arxiv.org/abs/math/0608694','https://arxiv.org/abs/math/0306142'})
config['steering']+='\n'+den['root_r486_scope']+'\n'+delta+'\n';save(ROOT/'r488-config.json',config)
spec=importlib.util.spec_from_file_location('discovery_constructor',ROOT/'prepare_discovery_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);ready=module.prepare(config)
allow=read(Path(ready['lane'])/'historical-results-allowlist.json')
for name in allow:
 rel=Path(name).relative_to(P)
 assert not any(t in part.lower() for part in rel.parts for t in forbidden)
 assert not any(part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r485-completion-boundary-delta.json',dict(utc=now,message=delta,new_protected_peer='expanded-corpus-r488',immutable_worker_inputs_unchanged=True))
print(json.dumps(dict(manifest_files=175,frozen_bindings=13,original_bindings=20,receipt_exit_counts=record['receipt_exit_counts'],disposition=record['root_disposition'],ready=ready)))
