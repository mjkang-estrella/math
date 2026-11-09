"""Root documentary verification of r520 (zero survivors) and the r522 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r520';assert not (P/'expanded-corpus-r522').exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==186
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=sorted(m['terminal_noncircular_self_exclusions']);assert set(aex)=={'MANIFEST.json','terminal_manifest_seal.receipt.json','terminal_manifest_seal.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r520.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))=={int(v['id']) for v in prov}
sources={}
for v in prov:
 raw,obj,token=corpus(v);key=str(obj['mathdb_id']);assert key==str(v['id']) and raw.decode()==v['raw_line_utf8']
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'] and gates[key]['literal']==obj['statement'];sources[key]=obj['source_url']
assert all(str(v['credit'])=='0' and v['qualified_survivor'] is False for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search-one-response.json','search-two-response.json','search-three-response.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=5,success=5),5)
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==904 and len(allow)==905 and set(hist)<=set(allow) and len(set(allow)-set(hist))==1
for name in hist:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482,521])

ass='r520 zero qualified survivors, no candidate, clean process record with no failed receipts. 339479: a full author join-of-pentagons negation was reconstructed but van Dam, Ge and Koolen 2606.19981v1 Theorem 5.3 already provides a public refutation at fixed t=5 and arbitrarily large order, and the author recorded the complete bridge and claimed nothing new. Strongest sustained incomplete routes: 365999 linear-cost maximal-system replacement, 352007 constrained short-tuple exact optimization and uniqueness, and 368090 ordered binomial-tail phases with uniform growing-index control, each with three routes and precise gaps. An O Neill dissertation lead is body-unread. Sixteen assigned original bodies unread; recorded parks are not open-status certifications. Verified 186 manifest files, 20 corpus bindings, 13 frozen, 904 saved history names, 5 GET successes (PDF), 3 searches / 9 strings with responses saved. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=186,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=904,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r547.json');den['utc']=now;den['root_r520_scope']=ass
save(P/'expanded-corpus-r520-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r548.json';save(denpath,den)

base=read(ROOT/'r521-config.json');active=['interval-kwidth-formal-sol-r2','expanded-corpus-r521']
base.update(number=522,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{520}),peer_routing_files=['selection-routing-interval-kwidth-formal-r2.json','selection-routing-r521.json','selection-routing-parking-strong-a2-formal-r1.json','selection-routing-high-girth-ur-matching-formal-r8.json'],denials=str(denpath))
base['steering']+='\n'+ass+'\n'+read(P/'interval-kwidth-formal-parent-integration-r1.json')['scientific_summary']+'\nActive and entirely protected: the 336276 formal r2 lane and r521. 323531 and 338806 stay under scientific hold with Lean paused. 57/60 unchanged.\n'
save(ROOT/'r522-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r522=module.prepare(base)
for name in read(Path(r522['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r522['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r520-r522-next-routing.json',dict(utc=now,discovery=r522,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r520_manifest=186,frozen=13,corpus=20,history=904,r522=r522,credit=0,accepted_new=57)))
