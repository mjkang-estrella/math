"""Root documentary verification of r527 (zero qualified survivors) and the r528 metadata packet with a tightened arithmetic selector. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast,importlib.util
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==57
A=P/'expanded-corpus-r527';assert not (P/'expanded-corpus-r528').exists()
def pick(v,*keys):
 for k in keys:
  if k in v:return v[k]
 raise KeyError(keys)

# Every documentary check precedes any root mutation.
m=read(A/'MANIFEST.json');assert len(m['files'])==214 and m['qualified_survivors']==0 and m['credit_claimed'] is False and m['formal_dispatch'] is False
names=set()
for n,x in m['files'].items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=m['terminal_noncircular_self_exclusions'];assert set(aex)=={'MANIFEST.json','MANIFEST.sha256','seal_own_lane.output.txt','seal_own_lane.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r527.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];gates=read(A/'results.json');assert len(ids)==len(gates)==20 and set(ids)==set(map(int,gates))
sources={}
for key,g in gates.items():
 v=read(A/g['provenance']);raw,obj,token=corpus(dict(v,chunk=pick(v,'chunk','path','chunk_path'),chunk_sha256=pick(v,'chunk_sha256'),line=int(pick(v,'line','one_based_line')),newline=pick(v,'newline','raw_newline'),raw_sha256=pick(v,'raw_sha256')))
 assert (A/g['raw']).read_bytes()==raw and obj['mathdb_id']==int(key) and g['literal']==obj['statement']
 assert dg(token)==pick(v,'statement_token_sha256','token_sha256','statement_raw_token_sha256','raw_statement_token_sha256') and dg(obj['statement'].encode())==pick(v,'statement_utf8_sha256','decoded_sha256','decoded_statement_utf8_sha256');sources[key]=obj['source_url']
assert all(str(v['credit_claimed'])=='False' and str(v['candidate_qualified'])=='False' for v in gates.values()) and not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=search(A,3,9,3,9,['search-response-1.json','search-response-2.json','search-response-3.json'])
ae=guard(A,list(A.glob('get-*.json')),ids,dict(attempt=5,success=5),4)
hist=read(A/'history-access.json');allow=read(A/'historical-results-allowlist.json');assert len(hist)==len(allow)==924 and set(hist)==set(allow)
for name in hist:
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482])

ass='r527 zero qualified survivors, no candidate, second round of the broadened pool. 353105 generalized Kaprekar height: an author tower-margin argument pays corrected height ranges, then an exact endpoint check at odd b>=5, n=2 finds a source-known endpoint correction, zero, with a routine-adaptation objection retained. 361986 and 361987 beta(N,l) keep exact period-attainment and diagonal gcd gaps; Newman 1959 is a specific unread lead, not an authenticated subsumer. 359519 Esser coprimality keeps the product-plus-one invariant and the even-dimensional branch unpaid. Sixteen assigned source works unread; recorded parks are not open-status certifications. Verified 214 manifest files, 20 corpus bindings, 13 frozen, 924 saved history names, 5 GET successes (4 PDF), 3 searches / 9 strings with responses saved. Credit 0, 57/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST.json'),task_reservation_genesis_verified=True,verified_manifest_files=214,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget,verified_saved_history_names=924,scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
den=read(ROOT/'inherited-denials-r560.json');den['utc']=now;den['root_r527_scope']=ass
save(P/'expanded-corpus-r527-parent-integration.json',ar);denpath=ROOT/'inherited-denials-r561.json';save(denpath,den)

# Tightened selector: the substring tags polynomial and matrix admitted deep areas such as Macdonald theory and matrix models.
sel=(ROOT/'reserve-broadened-finite-algebra-20261108-r526.py').read_text()
b0=re.search(r"^BROAD = \(.*\)\n",sel,re.M).group(0);d0=re.search(r"^DEEP = \(.*\)\n",sel,re.M).group(0)
b1="BROAD = ('number-theory','finite-fields','group-theory','finite-groups','semigroup','integer-sequence','digit','diophantine','divisib','arithmetic-function','prime','congruence','linear-algebra','matrix-analysis','discrete-geometry','convex-geometry')\n"
d1=d0.rstrip()[:-1]+",'macdonald','schubert','hall-littlewood','kazhdan','grothendieck','hessenberg','topological-recursion','matrix-model','alexander','operad','cohen-macaulay','calabi-yau','forcing','koszul','lie-type','character-theory','schur')\n"
sel=sel.replace(b0,b1).replace(d0,d1)
sel='# ROOT 2026-11-08 METADATA-ONLY TIGHTENING for r528: broad tags narrowed to elementary number theory and finite structures; more deep-area tags excluded. Not scientific review or clearance.\n'+sel
S=ROOT/'reserve-arithmetic-finite-20261108-r528.py';assert not S.exists();S.write_text(sel)

base=read(ROOT/'r527-config.json');active=['transitive-bunkbed-reach-formal-deepseek-r20','transitive-bunkbed-state-dominance-formal-sol-r21']
note='\n'+ass+'\nThis round is narrowed to elementary number theory and finite structures, because the previous two rounds spent reservations on deep algebraic areas. One recent candidate did survive an adversarial second review: it resolved a conjecture posed for a specific structured infinite family after the general statement had been refuted, by finding a small exact state summary that the structure makes sufficient. Look for that shape. 57/80 unchanged.\n'
base.update(number=528,protected_peers=active,completed_discovery_numbers=sorted(set(base['completed_discovery_numbers'])|{527}),peer_routing_files=sorted(set(base['peer_routing_files'])|{'selection-routing-r527.json','selection-routing-bunkbed-dominance-r21.json'}),denials=str(denpath),metadata_selector=str(S),metadata_selector_sha256=sha(S),steering=base['steering']+note)
save(ROOT/'r528-config.json',base);C=Path(base['metadata_constructor'])
spec=importlib.util.spec_from_file_location('discovery_target80',C);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);r=module.prepare(base)
for name in read(Path(r['lane'])/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(part in r['active_peers'] or part in {f'expanded-corpus-r{x}' for x in [395,463,466,482]}|{f'expanded-corpus-r{x}-parent-integration.json' for x in [395,463,466,482]} for part in rel.parts)
save(ROOT/'r527-r528-next-routing.json',dict(utc=now,discovery=r,credit=0,accepted_new=57,no_root_mathematics=True))
print(json.dumps(dict(r527_manifest=214,frozen=13,corpus=20,history=924,r528={k:r[k] for k in ['lane','ids','task_sha256','active_peers','target_new']},credit=0,accepted_new=57)))
