import json,re
from pathlib import Path
p=Path(__file__).resolve().parents[1];out={}
for name in ['source-citing','openai-tree','omega-tree']:
 f=p/'downloads'/name/'body'
 if not f.exists():out[name]={'error':'no body'};continue
 try:d=json.loads(f.read_text())
 except Exception:out[name]={'error':'not JSON'};continue
 if name=='source-citing':out[name]={'count':d.get('meta',{}).get('count'),'works':[{'id':x['id'],'title':x['title'],'doi':x['doi']} for x in d.get('results',[])]}
 else:out[name]={'sha':d.get('sha'),'truncated':d.get('truncated'),'paths':len(d.get('tree',[])),'hits':[x['path'] for x in d.get('tree',[]) if re.search('split.?graph|hamilton.?connect|tian.?dong|373598|2603.12770',x['path'],re.I)]}
(p/'outputs/final-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
