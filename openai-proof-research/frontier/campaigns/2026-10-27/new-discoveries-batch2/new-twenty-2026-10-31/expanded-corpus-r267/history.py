import json,re,subprocess,hashlib,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;root=next(x for x in p.parents if x.name=='openai-proof-research');d=json.loads((p/'literal-provenance.json').read_text());out={}
for i,x in d.items():
 r=x['record'];tokens=[r['source_url'].split('/abs/')[-1],r['title']];pat=r'\b'+i+r'\b|'+ '|'.join(re.escape(t) for t in tokens)
 z=subprocess.run(['rg','-n','-i','--max-count','5','--glob','*.md','--glob','*.json','--glob','*.txt','--glob','!reservation.json','--glob','!mathdb*','--glob','!routing*','--glob','!coverage*',pat,str(root/'frontier/campaigns/2026-10-27/new-discoveries-batch2')],capture_output=True,text=True,timeout=15)
 lines=[l for l in z.stdout.splitlines() if str(p) not in l and len(l)<4000];out[i]=lines
(p/'historical-hits.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
