"""Root documentary verification of r522 (zero survivors) and the r524 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r522';assert not (P/'expanded-corpus-r524').exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==178 and m['qualified_survivors']==0 and m['credit']==0
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=sorted(m['excluded']);assert set(aex)=={'MANIFEST.json','MANIFEST.sha256','seal_manifest.receipt.json','seal_manifest.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r522.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(v);assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj==v['object'] and obj['mathdb_id']==int(key)
 assert dg(token)==v['statement_raw_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'] and gates[key]['literal_statement']==obj['statement'];sources[key]=obj['source_url']
assert all(str(v['credit'])=='0' and v['qualified_survivor'] is False for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
assert gates['350111']['disposition']=='EXCLUDE_SOURCE_DEFINITION_CORRECTION' and gates['368617']['disposition']=='SOURCE_OWN_PUBLIC_SOLUTION' and gates['375407']['disposition']=='SOURCE_EXACT_PUBLIC_THEOREM'
abudget=search(A,2,6,3,9,['search1-response.json','search2-response.txt'])
ae=guard(A,list(A.glob('get-*-plan.json')),ids,dict(attempt=5,success=5),5)
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==908 and {x['path'] for x in hist}==set(allow)
for x in hist:
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,523]) and 'formal' not in x['path'].rsplit('/',1)[-1].lower()
 if x.get('sha256'):assert allow[x['path']]==x['sha256'],x['path']

ass='r522 zero qualified survivors, no candidate, clean process record with no failed receipts; first round selected under the finite-first instruction. 358850 has a complete incidence-image reduction but lacks a constant-slack mixed packet packing theorem; 382017 has exact single-edge stationarity and a coupled profile objective but lacks monotone compression or a sharp arbitrary-label bound, and its literal is asymptotic. 350111 is a source-definition correction, zero. 368617 and 375407 are proved in their own sources, zero. A specific 2026 Cichacz directed-labeling paper is unread and not an authenticated subsumer. Fifteen originals unread; recorded parks are not open-status certifications. Verified 178 manifest files, 20 corpus bindings, 13 frozen, 908 saved history entries, 5 GET successes (PDF), 2 searches / 6 strings with responses saved. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=178,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=908,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r550.json');den['utc']=now;den['root_r522_scope']=ass
save(P/'expanded-corpus-r522-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r551.json';save(denpath,den)

base=read(ROOT/'r523-config.json');active=['interval-kwidth-primary-qualification-sol-r2','expanded-corpus-r523']
base.update(number=524,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{522}),peer_routing_files=['selection-routing-interval-kwidth-qualification-r2.json','selection-routing-r523.json','selection-routing-parking-strong-a2-formal-r1.json','selection-routing-high-girth-ur-matching-formal-r8.json','selection-routing-interval-kwidth-formal-r2.json'],denials=str(denpath))
base['steering']+='\n'+ass+'\n'+read(P/'interval-kwidth-formal-parent-integration-r2.json')['scientific_summary']+'\nActive and entirely protected: the 336276 second qualification and r523. 57/60 unchanged.\n'
save(ROOT/'r524-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r524=module.prepare(base)
for name in read(Path(r524['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r524['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r522-r524-next-routing.json',dict(utc=now,discovery=r524,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r522_manifest=178,frozen=13,corpus=20,history=908,r524=r524,credit=0,accepted_new=57)))
