"""Root documentary verification of r521 (zero survivors) and the r523 metadata packet; no root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r521';assert not (P/'expanded-corpus-r523').exists()

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==215
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=sorted(m['terminal_noncircular_self_exclusions']);assert set(aex)=={'MANIFEST.json','SEAL.json','terminal_seal.receipt.json','terminal_seal.output.txt'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{'get_geodetic.receipt.json':1})
route=read(ROOT/'selection-routing-r521.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');prov=read(A/'literal-provenance.json');assert len(ids)==len(prov)==len(gates)==20 and set(ids)==set(map(int,gates))=={int(v['id']) for v in prov}
sources={}
for v in prov:
 raw,obj,token=corpus(v);key=str(obj['mathdb_id']);assert key==str(v['id']) and (A/'originals'/f'{key}.jsonl').read_bytes()==raw
 assert dg(token)==v['raw_statement_token_sha256'] and dg(obj['statement'].encode())==v['decoded_statement_utf8_sha256'] and gates[key]['literal_statement']==obj['statement'];sources[key]=obj['source_url']
assert collections.Counter(v['disposition'] for v in gates.values())=={'PARK_UNQUALIFIED':19,'PUBLIC_EXACT_RESULT_ZERO':1} and gates['331028']['disposition']=='PUBLIC_EXACT_RESULT_ZERO' and all(str(v['credit'])=='0' and v['qualified_survivor'] is False for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=5,success=4,unavailable=1),4)
un=next(e for e in ae if e['event']=='unavailable');assert un['status']==403 and 'oro.open.ac.uk' in un['url']
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');names_h={x['path'] for x in hist};assert len(hist)==905 and len(allow)==906 and names_h<=set(allow) and len(set(allow)-names_h)==1
for x in hist:
 rel=Path(x['path']).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,522])
 if x.get('sha256'):assert allow[x['path']]==x['sha256'],x['path']

ass='r521 zero qualified survivors, no candidate. 331028 has an exact public solution in a 2021 Annals paper, stronger than the assigned asymptotic, with deep dependencies attributed, zero. Sustained incomplete routes: 336091 support-free robustness rounding, 370014 fixed-k neighborly-code scaling, and 357454 complex discrepancy, where only the sharp trigonometric lower half is proved by the author and carries a stated routine-adaptation objection; the upper half is unpaid, so it is not a survivor. Seventeen assigned original sources unread; recorded parks are not open-status certifications. Verified 215 manifest files, 20 corpus bindings, 13 frozen, 905 saved history entries, 5 charged GET hops (4 PDF successes, 1 HTTP 403), 3 searches / 9 strings with responses saved. No formal dispatch or credit.'
work='Tuite, Erskine and Salia, Turan problems for k-geodetic digraphs, arXiv 2102.04957 all versions and Graphs and Combinatorics 39:25 final DOI 10.1007/s00373-023-02619-x'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 403 before any body; no retry or alternate recovery.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),seal_sha256=sha(A/'SEAL.json'),task_reservation_genesis_verified=True,verified_manifest_files=215,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,new_unavailable=read(A/'NEW-UNAVAILABLE.json'),verified_saved_history_names=905,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=aex,root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r548.json');den['utc']=now;den['root_r521_scope']=ass;den['root_geodetic_final_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un['url_key'],'arxiv.org/abs/2102.04957','arxiv.org/pdf/2102.04957','doi.org/10.1007/s00373-023-02619-x'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'2102.04957','10.1007/s00373-023-02619-x'})
den['records'].append(dict(url=un['url'],reason=dict(status=403,artifact=work,restriction=fs),evidence=dict(path=str(A/'NEW-UNAVAILABLE.json'),sha256=sha(A/'NEW-UNAVAILABLE.json'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r521-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r549.json';save(denpath,den)

base=read(ROOT/'r522-config.json');active=['interval-kwidth-formal-sol-r2','expanded-corpus-r522']
base.update(number=523,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{521}),peer_routing_files=['selection-routing-interval-kwidth-formal-r2.json','selection-routing-r522.json','selection-routing-parking-strong-a2-formal-r1.json','selection-routing-high-girth-ur-matching-formal-r8.json'],denials=str(denpath))
base['steering']+='\n'+ass+'\nActive and entirely protected: the 336276 formal r2 lane and r522. 57/60 unchanged.\n'
save(ROOT/'r523-config.json',base);constructor=Path(base['metadata_constructor']);assert sha(constructor)=='37d7074c7f226a4f4940ce2b5a59c57e2b1a39ffdc339f1917cab5e68549c76b';assert sha(Path(base['metadata_selector']))=='677992b5a6b1b17e45afbb3ae30f11548a37531593082819165278ee7d65ebed'
spec=importlib.util.spec_from_file_location('discovery_soft',constructor);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r523=module.prepare(base)
for name in read(Path(r523['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(t in part.lower() for part in rel.parts for t in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r523['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r521-r523-next-routing.json',dict(utc=now,discovery=r523,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r521_manifest=215,frozen=13,corpus=20,history=905,r523=r523,credit=0,accepted_new=57)))
