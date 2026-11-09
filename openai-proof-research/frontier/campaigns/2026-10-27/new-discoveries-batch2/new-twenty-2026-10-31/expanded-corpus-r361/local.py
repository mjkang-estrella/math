import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,datetime,time
L=pathlib.Path(__file__).resolve().parent; root=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); start=time.monotonic(); run=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'); out=[]
for rel in ['sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']:
 p=root/rel
 if p.exists():
  b=p.read_bytes(); t=b.decode(); out.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),matches=[s for s in t.splitlines() if any(w in s.lower() for w in ['derived','resistance','bidding','hypercube','registry','leanpool'])][:40]));
  if rel.endswith('upstream.json'): print(t)
 else:out.append(dict(path=str(p),missing=True))
p=L/'local-source-inventory.json'; assert p.resolve().is_relative_to(L); p.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,ensure_ascii=False)[:18000]); u=resource.getrusage(resource.RUSAGE_SELF); (L/('receipts/process-local-'+run+'.json')).write_text(json.dumps(dict(exit_code=0,wall_s=time.monotonic()-start,CPU_limit=120,AS_limit=6*1024**3,affinity=sorted(os.sched_getaffinity(0)),self_peak_RSS_KiB=u.ru_maxrss,self_CPU_s=u.ru_utime+u.ru_stime,external_wall_timeout=140,limitation='Self high water only')))
