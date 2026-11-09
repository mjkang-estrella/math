import json,hashlib,itertools as it
from pathlib import Path
root=Path(__file__).resolve().parents[1]
summary={}
for k in ['openai-head','omega-head','openalex-title','companion-citing','companion-openalex']:
 p=root/'downloads'/k/'body'
 if not p.exists():continue
 try:d=json.loads(p.read_text())
 except Exception:continue
 if k.endswith('head'):summary[k]={'sha':d.get('sha'),'date':d.get('commit',{}).get('committer',{}).get('date')}
 elif k=='companion-openalex':summary[k]={'id':d['id'],'locations':d['locations'],'open_access':d['open_access']}
 else:summary[k]={'count':d.get('meta',{}).get('count'),'works':[{'id':w['id'],'title':w['title'],'doi':w['doi'],'publication_date':w['publication_date']} for w in d.get('results',[])]}
# Explicit negative controls outside the admissible cyclic search bound.
controls=[]
for r,ms in [(4,range(8,13)),(5,range(12,16))]:
 for m in ms:
  good=0;count=0;mask=(1<<m)-1
  for tail in it.combinations(range(1,m),r-1):
   b=1+sum(1<<v for v in tail);count+=1
   good+=all((b&((b<<s|b>>(m-s))&mask)).bit_count()>=2 for s in range(1,m))
  assert good==0
  controls.append({'r':r,'m':m,'tested':count,'good':good})
summary['negative_controls']=controls
(root/'outputs/audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
