import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import runpy,sys,re
sys.argv=['research.py','audit'];d=runpy.run_path('research.py');L=d['L'];out={}
root=L.parents[4]
# Exact immutable-source routing paths, never any historical or active lane scan.
for n in ['upstream.json','CONTENTS.md']:
 p=root/'sources'/n
 if p.exists():
  b=p.read_bytes();s=b.decode();out[n]={'path':str(p),'sha256':d['H'](b),'bytes':len(b)}
  if n.endswith('json'):out[n]['record']=d['json'].loads(s)
  else:out[n]['matches']=[line for line in s.splitlines() if not 'crown' in line.lower() and any(t in line.lower() for t in ['semicomplete','grothendieck polynomial','rayleigh difference','gabow','021-avoid','borel csp','prime gap graph'])]
 else:out[n]={'path':str(p),'error':'not present at expected exact path'}
for n in ['leanpool-page.html']:
 s=(L/'sources'/n).read_text();out[n]={'heads':re.findall(r'currentOid":"([0-9a-f]{40})',s)[:1]}
for n in ['leanpool-projects.yml','leanpool-index.lean','openai-formalization.yaml','openai-overview.tex']:
 b=(L/'sources'/n).read_bytes();s=b.decode();out[n]={'sha256':d['H'](b),'read_depth':'bounded keyword routing only; no absence or proof clearance','matches':[line[:4000] for line in s.splitlines() if not 'crown' in line.lower() and any(t in line.lower() for t in ['semicomplete','grothendieck polynomial','rayleigh difference','gabow','021-avoid','borel csp','prime gap graph'])]}
d['dump']('registry-check.json',out);print(d['json'].dumps(out,indent=2)[:3000]);d['receipt']('registry-audit')
