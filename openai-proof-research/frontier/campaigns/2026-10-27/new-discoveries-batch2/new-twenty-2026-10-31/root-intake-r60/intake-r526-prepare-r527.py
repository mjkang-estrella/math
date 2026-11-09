"""Root documentary verification of r526 (zero qualified survivors) and the r527 metadata packet. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r526';assert not (P/'expanded-corpus-r527').exists()

# Every documentary check precedes any root mutation.
m=read(A/'manifest.json');assert len(m['files'])==202==m['file_count'] and m['qualified_survivors']==0
names=set()
for n,h in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==h,n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'manifest.json','seal.output.txt','seal.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{'get_hu_public.receipt.json':1})
route=read(ROOT/'selection-routing-r526.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==len(gates)==20 and set(ids)==set(map(int,gates))
sources={}
for key in gates:
 v=read(A/'provenance'/f'{key}.json');raw,obj,token=corpus(v);assert (A/'originals'/f'{key}.jsonl').read_bytes()==raw and obj['mathdb_id']==int(key)
 assert token.decode()==v['statement_token'] and dg(token)==v['statement_token_sha256'] and dg(obj['statement'].encode())==v['statement_utf8_sha256'] and gates[key]['literal']==obj['statement'];sources[key]=obj['source_url']
assert all(str(v['credit_claim'])=='0' for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
assert gates['335512']['status']=='PUBLIC_THEOREM_ZERO' and gates['335511']['status']=='PUBLIC_THEOREM_ZERO' and gates['328016']['status']=='SPECIFIC_PUBLIC_REFUTATION_BODY_HOLD' and gates['341858']['status']=='CORRECTION_ZERO_GENERIC_INTENDED_PROOF'
abudget=search(A,3,9,3,9,['search1-response.json','search2-response.json','search3-response.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=6,success=5,unavailable=1),5)
un=next(e for e in ae if e['event']=='unavailable');assert un['status']==403 and un['url_key']=='www.preprints.org/manuscript/202610.1039'
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==919 and {x['path'] for x in hist}==set(allow)
for x in hist:
 rel=Path(x['path']).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in x['path'] for z in [395,463,466,482,525]) and 'lean-address' not in x['path']

ass='r526 zero qualified survivors, no candidate, first round from the broadened number-theory and finite-algebra pool. 335512 is the exact public double-Schubert SNP theorem of Fink, Meszaros and St. Dizier and 335511 follows from it, zero. 341858 has an author-complete moment-rank proof of the intended statement, but it corrects the extracted j=0 formula and falls under a generic rank law, zero. 333496 is a correction, with the intended statement parked. 328016 has a specific October 2026 public refutation claim by Xing-Yu Hu whose body returned HTTP 403, a HOLD rather than an authenticated exclusion. Vill generic reduction, nonzero-alpha Niho classification and prime v-palindromes retain precise gaps. Sixteen assigned source works unread; recorded parks are not open-status certifications. Verified 202 manifest files, 20 corpus bindings, 13 frozen, 919 saved history entries, 6 charged GET hops (5 PDF successes, 1 HTTP 403), 3 searches / 9 strings with responses saved. Credit 0, 57/80.'
work='Xing-Yu Hu, Full-Support Solutions and Rigidity for Three-Dimensional Evolution Algebras, preprints.org 202610.1039'
fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after HTTP 403; no retry.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),task_reservation_genesis_verified=True,verified_manifest_files=202,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=919,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r558.json');den['utc']=now;den['root_r526_scope']=ass;den['root_hu_preprint_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un['url_key'],'preprints.org/manuscript/202610.1039'});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower(),'202610.1039'})
den['records'].append(dict(url=un['url'],reason=dict(status=403,artifact=work,restriction=fs),evidence=dict(path=str(A/'NETWORK-STOP.md'),sha256=sha(A/'NETWORK-STOP.md'),guard_sha256=sha(A/'guard-ledger.jsonl'))))
save(P/'expanded-corpus-r526-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r559.json';save(denpath,den)

base=read(ROOT/'r526-config.json');active=['transitive-bunkbed-reach-formal-deepseek-r20','transitive-bunkbed-primary-qualification-sol-r2']
note='\n'+read(P/'expanded-corpus-r525-parent-integration.json')['scientific_summary']+'\n'+ass+'\nLEAN UPDATE, superseding earlier notes: the address-space diagnostic is SUPPORTED. Lean modules importing Complex, Polynomial, Ideal quotients and Real now compile and pass kernel checks here under the raised limit; only a whole-library import of Mathlib is excluded. A target is no longer disqualified because its endpoint is algebraic. This lane still runs no Lean. 382297 is under separate protected work. 57/80 unchanged.\n'
base.update(number=527,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{525,526}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r525.json','selection-routing-r526.json','selection-routing-bunkbed-deepseek-r20.json','selection-routing-bunkbed-qualification-r2.json'}),denials=str(denpath),steering=base['steering']+note)
save(ROOT/'r527-config.json',base);C=Path(base['metadata_constructor'])
spec=importlib.util.spec_from_file_location('discovery_target80',C);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r=module.prepare(base)
for name in read(Path(r['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r526-r527-next-routing.json',dict(utc=now,discovery=r,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r526_manifest=202,frozen=13,corpus=20,history=919,new_closure=un['url'],r527={k:r[k] for k in ['lane','ids','task_sha256','active_peers','target_new']},credit=0,accepted_new=57)))
