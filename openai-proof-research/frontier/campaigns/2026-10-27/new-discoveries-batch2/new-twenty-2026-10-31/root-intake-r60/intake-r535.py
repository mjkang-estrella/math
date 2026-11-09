"""Root documentary verification of r535 (zero qualified survivors). No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==58
A=P/'expanded-corpus-r535'
def pick(v,*keys):
 for k in keys:
  if k in v:return v[k]
 raise KeyError(keys,list(v))
m=read(A/'MANIFEST-SEAL.json');assert m['file_count']==213==len(m['files']) and m['self_excluded']=='MANIFEST-SEAL.json'
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['size'],n
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
extra=inventory-names;assert names<=inventory and 'MANIFEST-SEAL.json' in extra and all(x=='MANIFEST-SEAL.json' or 'seal' in x.lower() for x in extra),extra
frozen(A,13);arec=receipts(A,{})
route=read(ROOT/'selection-routing-r535.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];res=read(A/'results.json');gates=res.get('gates') or res.get('results');assert len(ids)==len(gates)==20 and set(ids)==set(map(int,gates))
root=P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus';sources={}
for key,g in gates.items():
 v=g['literal'];q=root/Path(pick(v,'chunk_file','chunk')).name
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(pick(v,'chunk_line_one_based','line_one_based','line'))-1];assert raw.endswith(b'\n') and dg(raw.rstrip(b'\n'))==v['raw_line_sha256']  # the lane labels this hash as including the newline, but it does not; root verified all twenty without it
 obj=json.loads(raw);assert obj['mathdb_id']==int(key);sources[key]=obj['source_url']
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*'))
abudget=read(A/'search-budget.json');assert abudget==dict(calls_used=2,queries_used=6,maximum_calls=3,maximum_queries=9,charged_before_call=True)
abudget2=search(A,2,6,3,9,['searches/search-response-001.txt','searches/search-response-002.txt'])
ae=guard(A,sorted(A.glob('plans/get-*.json')),ids,dict(attempt=4,success=4),4)
for name in read(A/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
ass='r535 zero qualified survivors, DeepSeek lane that did use its network budget. 364214 keeps a precise gap at a per-step cancellation of order n. 344498 derives a stabiliser dichotomy and the hard parameter region, with small instances excluded, and a gap at nonabelian Kneser. 360918 bounds only degree at most 2 cards. 382400 and 356524 are dead by source ownership as the literal records. Fifteen parked. Root correction: the lane says its raw_line_sha256 includes the trailing newline, but all twenty hashes match the corpus lines without it; the bindings are correct and only the label is wrong. Verified 213 manifest files, 20 corpus bindings, 13 frozen, 4 GET successes (all PDF), 2 searches / 6 strings with responses saved. Credit 0, 58/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'MANIFEST-SEAL.json'),task_reservation_genesis_verified=True,verified_manifest_files=213,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(collections.Counter(e['event'] for e in ae)),search_budget=abudget2,model='spark/DeepSeek-V4.1-Flash-1017',scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS',credit=0,accepted_new=58,terminal_self_exclusions=sorted(extra),root_scope='Documentary integrity only; no mathematical execution by root.')
save(P/'expanded-corpus-r535-parent-integration.json',ar)
den=read(ROOT/'inherited-denials-r572.json');den['utc']=now;den['root_r535_scope']=ass;save(ROOT/'inherited-denials-r573.json',den)
print(json.dumps(dict(r535_manifest=213,frozen=13,corpus=20,extra=sorted(extra),credit=0,accepted_new=58)))
