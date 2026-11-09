"""Root documentary verification of r516 (procedural FAIL, zero survivors) and the r518 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r516';assert not (P/'expanded-corpus-r518').exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==145 and str(m['qualified_survivors'])=='0' and m['process_status'].startswith('FAIL')
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'MANIFEST.json','seal_run.output.txt','seal_run.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r516.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))==set(map(int,prov))
sources={}
for key,v in prov.items():
 raw,obj,token=corpus(v);assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and obj['statement']==v['statement_utf8'] and dg(obj['statement'].encode())==v['statement_utf8_sha256']
 assert gates[key]['literal_statement']==obj['statement'];sources[key]=obj['source_url']
assert collections.Counter(v['disposition'] for v in gates.values())=={'PROCEDURAL_FAIL_UNQUALIFIED_PARK':20} and all(str(v['credit'])=='0' and v['qualified_survivor'] is False for v in gates.values())
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
budget=read(A/'search-budget.json');assert budget==dict(calls_used=1,queries_used=3,maximum_calls=3,maximum_queries=9,charged_before_call=True)
charges=[json.loads(s) for s in (A/'search-charges.jsonl').read_text().splitlines()];assert len(charges)==1 and charges[0]['plan']=='search1.json' and sha(A/'search1.json')==charges[0]['plan_sha256'] and read(A/'search1.json')['queries']==charges[0]['queries'] and sha(A/'charge_search.py')==sha(ROOT/'charge_search.py')
assert not list(A.glob('*respon*')) and 'Procedural FAIL' in (A/'NETWORK-STOP.md').read_text()
ae=guard(A,[A/n for n in ['get-cards.json','get-codes.json','get-tree.json']],ids,dict(attempt=2,success=2),2)
history=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(history)==len(allow)==893 and set(history)==set(allow)
for name in history:
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482,517])

ass='r516 PROCEDURAL FAIL, zero qualified survivors, no candidate. One native search was precharged for three strings and invoked once; its full response was displayed but not saved, cannot be reconstructed from snippets and is recorded as missing. No rerun, refund or counter reset; network stopped on recognition, leaving one unexecuted GET plan. Treated as a procedural failure and not quarantined, following the earlier missing-search-response precedent; all twenty packets are unqualified, and any later use of these targets needs fresh source and prior checks. Complete TASK and denials were personally read in chunks first. 354942 and 330531 have sustained incomplete routes: an unproved occupation-reward lemma, and a MAP-versus-iterative decoding gap with a source-owned pivotal-boundary obstruction. The finite tensor lemma is a helper with zero credit. 331435 is blocked on the source Q order. Reported public resolutions for 324023 and 375140 are leads only. Eighteen assigned bodies unread. Verified 145 manifest files, 20 corpus bindings, 13 frozen, 893 saved history names, 2 GET successes (PDF), 1 search / 3 strings. No formal dispatch or credit.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=145,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=budget,search_response_missing=True,verified_saved_history_names=893,scientific_summary=ass,root_disposition='PROCEDURAL_FAIL_ZERO_QUALIFIED_SURVIVORS_NOT_QUARANTINED',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r536.json');den['utc']=now;den['root_r516_scope']=ass
save(P/'expanded-corpus-r516-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r537.json';save(denpath,den)

base=read(ROOT/'r517-config.json');active=['high-girth-ur-matching-formal-sol-r7','expanded-corpus-r517']
base.update(number=518,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{516}),peer_routing_files=['selection-routing-high-girth-ur-matching-formal-r7.json','selection-routing-r517.json','selection-routing-parking-strong-a2-formal-r1.json'],denials=str(denpath))
base['steering']+='\n'+read(P/'high-girth-ur-matching-formal-parent-integration-r6.json')['scientific_summary']+'\n'+ass+'\nRoot continues uncredited 338806 formal research r7, not a scientific PASS, acceptance or source waiver; all formal bodies and flat metadata are protected from discovery. r517 is active and entirely protected. 57/60 unchanged.\n'
save(ROOT/'r518-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r518=module.prepare(base)
for name in read(Path(r518['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r518['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r516-r518-next-routing.json',dict(utc=now,discovery=r518,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r516_manifest=145,frozen=13,corpus=20,history=893,r518=r518,credit=0,accepted_new=57)))
