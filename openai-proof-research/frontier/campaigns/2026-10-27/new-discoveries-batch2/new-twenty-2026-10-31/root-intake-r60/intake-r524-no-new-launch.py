"""Root documentary verification of r524 (zero survivors). No new lane is prepared: root recommended stopping new twenty-problem rounds and awaits the user. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,base64
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r524'

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==155 and m['status']=='sealed_zero_qualified_survivors'
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'MANIFEST.json','seal_manifest.receipt.json','seal_manifest.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{'cross_read_1_get_semi.receipt.json':1})
route=read(ROOT/'selection-routing-r524.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'corpus-bindings.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(dict(v,newline=v['raw_newline']),pathfield='path');assert base64.b64decode(v['raw_base64'])==raw and obj==v['object'] and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_raw_token'] and dg(token)==v['statement_raw_token_sha256'] and obj['statement']==v['statement_utf8'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'] and gates[key]['literal']==obj['statement'];sources[key]=obj['source_url']
assert all(str(v['credit'])=='0' for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search-response-1.txt','search-response-2.txt','search-response-3.txt'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=6,success=5,unavailable=1),5)
un=next(e for e in ae if e['event']=='unavailable');assert un['status']==404 and 'furedi' in un['url']
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==912 and set(hist)==set(allow)
for name in hist:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482]) and 'focused-finite' not in name

ass='r524 zero qualified survivors, no candidate. 381983: an author 24-vertex, 60-edge planar negation was reconstructed but is the public Fang, Lin and Shi outerplanar-cone family, zero. 354635 is settled by an exact public Bastide, Groenland, Jacob and Johnston theorem, zero. 382107 cross-Sperner has three incomplete routes and lacks a multiway inequality or compression lemma. A Kuperus thesis lead is body-unread. Seventeen assigned source works unread; recorded parks are not open-status certifications. Verified 155 manifest files, 20 corpus bindings, 13 frozen, 912 saved history names, 6 charged GET hops (5 PDF successes, 1 HTTP 404), 3 searches / 9 strings with responses saved. No formal dispatch or credit. Root prepares no further twenty-problem round at this point.'
work='Furedi and Kim, Cycle-saturated graphs with minimum number of edges, arXiv 1103.0067 all versions and final'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 404 at the observed author URL; no retry.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=155,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,new_unavailable=read(A/'NEW-UNAVAILABLE.json'),verified_saved_history_names=912,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r553.json');den['utc']=now;den['root_r524_scope']=ass;den['root_furedi_kim_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un['url_key'],'arxiv.org/abs/1103.0067','arxiv.org/pdf/1103.0067'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'1103.0067'})
den['records'].append(dict(url=un['url'],reason=dict(status=404,artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r524-parent-integration.json',ar);save(ROOT/'inherited-denials-r554.json',den)
save(ROOT/'r524-intake-report.json',dict(utc=now,files=155,frozen=13,corpus_bindings=20,history_names=912,credit=0,accepted_new=57,no_root_mathematics=True,slot_left_open=True,slot_left_open_reason='Root recommended to the user that new twenty-problem rounds stop after r524 and the focused lane, and is awaiting a reply; no other queued work is available below the Lean kernel-check wall.',still_running=['focused-finite-routes-sol-r1','parking-strong-a2-primary-qualification-sol-r2']))
print(json.dumps(dict(r524_manifest=155,frozen=13,corpus=20,history=912,new_closure=un['url'],slot_left_open=True,credit=0,accepted_new=57)))
