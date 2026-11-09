"""Root documentary verification of r528 (zero qualified survivors) and the r529 metadata packet. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r528';assert not (P/'expanded-corpus-r529').exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==170 and m['qualified_survivors']==0 and m['credit']==0 and m['failed_receipts']==[]
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_self_exclusions'];assert set(aex)=={'MANIFEST.json','seal_lane.receipt.json','seal_lane.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r528.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(gates)==len(prov)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(dict(v,raw_sha256=v['raw_line_sha256'],line=int(v['line'])));assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj==v['object'] and obj['mathdb_id']==int(key)
 assert token.decode()==v['raw_statement_token'] and dg(token)==v['raw_statement_token_sha256'] and dg(obj['statement'].encode())==v['decoded_statement_sha256'];sources[key]=obj['source_url']
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search-response-1.json','search-response-2.json','search-response-3.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=4,success=4),4)
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==926 and set(hist)==set(allow)
for name in hist:
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482])

ass='r528 zero qualified survivors, no candidate, first round of the narrowed arithmetic pool. 319405 has an author-complete literal negation, pi=(3,2,2,2,1) in C5, but a complete bridge to Nagy\'s public translated exceptional structure makes it a zero-credit normalization correction; the intended prescribed-value classification is unpaid. 323448 ceiling recursions and 373679 Pinn endpoints each retain precise unpaid lemmas after three routes. Seventeen assigned source works unread; recorded parks are not open-status certifications. Verified 170 manifest files, 20 corpus bindings, 13 frozen, 926 saved history names, 4 GET successes (all PDF), 3 searches / 9 strings with responses saved. Credit 0, 57/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=170,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=926,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r561.json');den['utc']=now;den['root_r528_scope']=ass
save(P/'expanded-corpus-r528-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r562.json';save(denpath,den)

base=read(ROOT/'r528-config.json');active=['transitive-bunkbed-reach-formal-deepseek-r20','transitive-bunkbed-state-dominance-formal-sol-r22']
base.update(number=529,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{528}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r528.json','selection-routing-bunkbed-dominance-r22.json'}),denials=str(denpath),steering=base['steering']+'\n'+ass+'\n')
save(ROOT/'r529-config.json',base);C=Path(base['metadata_constructor'])
spec=importlib.util.spec_from_file_location('discovery_target80',C);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r=module.prepare(base)
for name in read(Path(r['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r528-r529-next-routing.json',dict(utc=now,discovery=r,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r528_manifest=170,frozen=13,corpus=20,history=926,r529={k:r[k] for k in ['lane','ids','task_sha256','active_peers','target_new']},credit=0,accepted_new=57)))
