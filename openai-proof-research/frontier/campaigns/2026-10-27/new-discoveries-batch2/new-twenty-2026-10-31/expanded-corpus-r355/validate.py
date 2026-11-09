import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib
p=pathlib.Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_bytes()); assert h((p/'reservation.json').read_bytes())=='ff5b598a3d7bf11c8fef0336ea5e75de16f1d564ae5bff8c72ab2d59df1e0713'
x=json.loads((p/'results.json').read_bytes()); v=json.loads((p/'provenance.json').read_bytes()); assert set(x)==set(v)==set(map(str,r['ids'])) and len(x)==20
for k,o in v.items():
 b=(p/'literal'/(k+'.jsonl')).read_bytes(); assert b.endswith(b'\n') and h(b)==o['raw_sha256']; assert json.loads(b)==o['record']==x[k]['full_record']; assert h(o['record']['statement'].encode())==o['statement_sha256']; assert x[k]['credit']==0
# Recheck each unique literal source chunk, without any historical/protected scan.
for path in set(o['chunk'] for o in v.values()):
 q=pathlib.Path(path); b=q.read_bytes(); lines=b.splitlines(keepends=True)
 for k,o in v.items():
  if o['chunk']==path: assert h(b)==o['chunk_sha256'] and lines[o['line']-1]==(p/'literal'/(k+'.jsonl')).read_bytes()
print(json.dumps({'exact20':True,'raw_newlines':True,'full_records':True,'statement_hashes':True,'chunk_hashes_and_one_based_lines':True,'reservation_unchanged':True,'credit':0,'rusage_self':list(resource.getrusage(resource.RUSAGE_SELF))}))
