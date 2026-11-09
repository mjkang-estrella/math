"""Generic root documentary verification of a discovery lane, tolerant of the field names lanes choose. Arguments: number summary_file denials_in denials_out expected_failed_labels(comma) disposition. No root mathematics."""
import os,resource,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,collections,ast
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
num,sfile,dinn,dout,fails,disp=sys.argv[1:7];A=P/f'expanded-corpus-r{num}';now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json')
mp=next(q for q in [A/'MANIFEST.json',A/'manifest.json',A/'MANIFEST-SEAL.json',A/'SHA256-MANIFEST.json',A/'MANIFEST.sha256.json'] if q.exists());m=read(mp);fs=m.get('files',m.get('sha256'));rows={x['path']:x for x in fs} if isinstance(fs,list) else {k:(v if isinstance(v,dict) else dict(sha256=v)) for k,v in fs.items()}
for n,x in rows.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'],n
 b=x.get('bytes',x.get('size'))
 if b is not None:assert q.stat().st_size==b,n
inventory={str(q.relative_to(A)) for q in A.rglob('*') if q.is_file()};extra=inventory-set(rows);assert set(rows)<=inventory and len(extra)<=6 and mp.name in extra,extra
frozen(A,13);expected={x+'.receipt.json':1 for x in fails.split(',') if x};arec=receipts(A,expected)
route=read(ROOT/f'selection-routing-r{num}.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids']
def norm(b):
 b=b.get('bindings',b.get('rows',b)) if isinstance(b,dict) and ('bindings' in b or 'rows' in b) else b
 return {str(x.get('id',x.get('mathdb_id'))):x for x in b} if isinstance(b,list) else b
bf=next((q for q in [A/'literal-bindings.json',A/'corpus-bindings.json',A/'literals.json',A/'literal-provenance.json'] if q.exists()),None);res=read(A/'results.json');gates=res.get('gates',res.get('results',res)) if isinstance(res,dict) else res
assert isinstance(gates,dict) and set(ids)==set(map(int,gates)) and len(gates)==20
bind=norm(read(bf)) if bf else {k:g.get('literal') or g.get('provenance') for k,g in gates.items()};root=P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus';sources={}
def pick(v,*keys):
 for k in keys:
  if k in v:return v[k]
 raise KeyError(keys,list(v))
checked=0
for key in map(str,ids):
 v=bind[key];c=Path(pick(v,'chunk','chunk_file','chunk_path','path'));q=c if c.is_absolute() else root/c.name;assert q.is_relative_to(root)
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(pick(v,'line_one_based','chunk_line_one_based','line_1based','one_based_line','line'))-1];s=pick(v,'raw_line_sha256_with_newline','raw_line_with_newline_sha256','raw_line_sha256_including_newline','raw_line_sha256','raw_sha256');assert s in (dg(raw),dg(raw.rstrip(b'\n'))),key
 obj=json.loads(raw);assert obj['mathdb_id']==int(key);sources[key]=obj['source_url'];checked+=1
budget=read(A/'search-budget.json');charges=[json.loads(x) for x in (A/'search-charges.jsonl').read_text().splitlines()];assert budget['calls_used']==len(charges)<=budget['maximum_calls'] and all(sha(A/c['plan'])==c['plan_sha256'] for c in charges)
ledger=[json.loads(x) for x in (A/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in ledger);pdfs=sum((A/e['destination']).read_bytes().startswith(b'%PDF') for e in ledger if e['event']=='success')
plans=sorted(set(A.glob('plans/get-*.json'))|set(A.glob('get-*.json'))|set(A.glob('plans/*get*.json')));ge=guard(A,plans,ids,dict(counts),pdfs)
for name in read(A/'historical-results-allowlist.json'):
 rel=Path(name).relative_to(P);assert not any(w in part.lower() for part in rel.parts for w in ['formal','code-loop','code_loop','polynexus','crown','bunkbed','tournament','hat-bipartite'])
 assert not any(f'expanded-corpus-r{z}' in name for z in [395,463,466,482])
s=Path(sfile).read_text().strip()
save(P/f'expanded-corpus-r{num}-parent-integration.json',dict(utc=now,source_lane=str(A),manifest_sha256=sha(mp),task_reservation_genesis_verified=True,verified_manifest_files=len(rows),verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,all20_gates=gates,runner_receipts=arec,guard_events=dict(counts),search_budget=budget,scientific_summary=s,root_disposition=disp,credit=0,accepted_new=led['accepted_new'],terminal_self_exclusions=sorted(extra),root_scope='Documentary integrity only; no mathematical execution by root.'))
den=read(ROOT/dinn);den['utc']=now;den[f'root_r{num}_scope']=s;save(ROOT/dout,den)
print(json.dumps(dict(num=num,manifest=len(rows),corpus=checked,frozen=13,receipts=len(arec),guard=dict(counts),pdfs=pdfs,search=budget['calls_used'],extra=sorted(extra),accepted_new=led['accepted_new'])))
