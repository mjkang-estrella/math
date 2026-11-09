"""Root documentary verification of r517 (zero survivors) and the r519 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util,base64
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r517';assert not (P/'expanded-corpus-r519').exists()

# Every documentary check precedes any root mutation.
aex=manifest(A,'MANIFEST.json',164,'manifest_seal','terminal_non_circular_self_exclusions');frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r517.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'original-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))=={int(v['id']) for v in prov}
sources={}
for v in prov:
 raw,obj,token=corpus(v);key=str(obj['mathdb_id']);assert key==str(v['id']) and key in gates and base64.b64decode(v['raw_base64'])==raw and obj==v['object']
 assert base64.b64decode(v['statement_token_base64'])==token and dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'];sources[key]=obj['source_url']
assert collections.Counter(v['disposition'] for v in gates.values())=={'PARK_PRECISE_GAP':18,'EXCLUDE_PUBLIC':2} and all(str(v['credit'])=='0' and not v['qualified_survivor'] for v in gates.values())
assert {k for k,v in gates.items() if v['disposition']=='EXCLUDE_PUBLIC'}=={'350682','367538'} and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,2,6,3,9,['search1-response.json','search2-response.json'])
ae=guard(A,[A/n for n in ['get-coedge.json','get-components.json','get-even.json','get-harary.json','get-hst.json','get-matching-public.json','get-matching.json']],ids,dict(attempt=7,success=7),6)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==len(allow)==894 and {x['path'] for x in history}==set(allow)
for x in history:
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,518]) and 'formal' not in x['path'].rsplit('/',1)[-1].lower()
 if x.get('sha256'):assert allow[x['path']]==x['sha256'],x['path']

ass='r517 zero qualified survivors, no candidate, clean process record with no failed receipts. 350682 is the exact public Hogan-Scott-Tsarev 2604.09449v2 result, actual theorem and proof read, zero. 367538 is the original source own infinite counterexample family, zero. Strongest unresolved: 372265 arbitrary-property Harary uniqueness, 364944 all-H even-decomposability dichotomy, 370089 exact all-r component edge-load inequality, each with three routes and precise gaps, none promoted. Eighteen targets PARK with precise gaps; fifteen assigned original bodies unread and their recorded gaps are not open-status certifications. Complete TASK and denials read in chunks before network. Verified 164 manifest files, 20 corpus bindings, 13 frozen, 894 saved history entries, 7 GET successes (6 PDF, 1 HTML), 2 searches / 6 strings with responses saved. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=164,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=894,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r537.json');den['utc']=now;den['root_r517_scope']=ass
save(P/'expanded-corpus-r517-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r538.json';save(denpath,den)

base=read(ROOT/'r518-config.json');active=['high-girth-ur-matching-formal-sol-r7','expanded-corpus-r518']
base.update(number=519,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{517}),peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r7.json','selection-routing-r518.json','selection-routing-parking-strong-a2-formal-r1.json'],denials=str(denpath))
base['steering']+='\n'+ass+'\nr518 is active and entirely protected. 57/60 unchanged.\n'
save(ROOT/'r519-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r519=module.prepare(base)
for name in read(Path(r519['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r519['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r517-r519-next-routing.json',dict(utc=now,discovery=r519,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r517_manifest=164,frozen=13,corpus=20,history=894,r519=r519,credit=0,accepted_new=57)))
