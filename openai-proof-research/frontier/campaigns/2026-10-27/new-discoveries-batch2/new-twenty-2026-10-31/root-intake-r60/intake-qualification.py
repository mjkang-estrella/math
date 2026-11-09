"""Generic root documentary verification and disposition of an independent qualification lane. Arguments: mathdb_id lane integration_name disposition summary_file denials_in denials_out expected_failed_labels(comma) [ledger_exclusion_note]. No root mathematics."""
import os,resource,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,collections
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
mid,lane,iname,disp,sfile,dinn,dout,fails=sys.argv[1:9];note=sys.argv[9] if len(sys.argv)>9 else None
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');Q=P/lane;rdy=read(ROOT/f'qualification-{mid}-ready.json');assert rdy['lane']==str(Q)
m=read(Q/'MANIFEST.json');fs=m['files'];rows={x['path']:x for x in fs} if isinstance(fs,list) else {k:(v if isinstance(v,dict) else dict(sha256=v)) for k,v in fs.items()}
for n,x in rows.items():
 assert not Path(n).is_absolute() and '..' not in Path(n).parts;q=Q/n;assert not q.is_symlink() and sha(q)==x['sha256'],n
 if 'bytes' in x:assert q.stat().st_size==x['bytes'],n
ek=[k for k in m if 'xclu' in k and isinstance(m[k],(list,dict))];assert len(ek)==1;ex=m[ek[0]];ex=sorted(ex) if not (isinstance(ex,list) and ex and isinstance(ex[0],dict)) else sorted(x['path'] for x in ex)
inventory=set()
for q in Q.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(Q)))
assert set(rows)<=inventory and inventory-set(rows)<=set(ex) and 'MANIFEST.json' in ex and len(ex)<=5
frozen(Q,rdy['frozen_bindings']);assert sha(Q/'TASK.txt')==rdy['task_sha256']
expected={x+'.receipt.json':1 for x in fails.split(',') if x};qrec=receipts(Q,expected)
budget=read(Q/'search-budget.json');charges=[json.loads(s) for s in (Q/'search-charges.jsonl').read_text().splitlines()];assert budget['calls_used']==len(charges)<=budget['maximum_calls'] and budget['charged_before_call'] is True and all(sha(Q/c['plan'])==c['plan_sha256'] for c in charges)
ledger=[json.loads(l) for l in (Q/'guard-ledger.jsonl').read_text().splitlines()];counts=collections.Counter(e['event'] for e in ledger);pdfs=sum((Q/e['destination']).read_bytes().startswith(b'%PDF') for e in ledger if e['event']=='success')
ge=guard(Q,sorted(set(Q.glob('plans/get-*.json'))|set(Q.glob('get-*plan*.json'))|set(Q.glob('plans/*get*.json'))),[int(mid)],dict(counts),pdfs)
review=read(Q/'review.json');g=review[mid] if mid in review else review;assert str(g.get('id',g.get('mathdb_id',g.get('target',mid))))==mid and str(g.get('credit','0')).startswith('0')
s=Path(sfile).read_text().strip()
save(P/iname,dict(utc=now,mathdb_id=int(mid),source_lane=str(Q),manifest_sha256=sha(Q/'MANIFEST.json'),verified_manifest_files=len(rows),verified_frozen_bindings=rdy['frozen_bindings'],review=g,runner_receipts=qrec,guard_events=dict(counts),search_budget=budget,scientific_summary=s,reviewer_recommendation=g.get('recommendation'),root_disposition=disp,credit=0,accepted_new=led['accepted_new'],terminal_self_exclusions=ex,root_scope='Documentary integrity and scientific disposition only; no mathematics by root.'))
den=read(ROOT/dinn);den['utc']=now;den[f'root_qualification_{mid}_scope']=s;save(ROOT/dout,den)
if note:
 led['excluded_after_review'][mid]=note;(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
print(json.dumps(dict(mid=mid,manifest=len(rows),frozen=rdy['frozen_bindings'],receipts=len(qrec),guard=dict(counts),pdfs=pdfs,search=budget['calls_used'],recommendation=g.get('recommendation'),disposition=disp,accepted_new=led['accepted_new'])))
