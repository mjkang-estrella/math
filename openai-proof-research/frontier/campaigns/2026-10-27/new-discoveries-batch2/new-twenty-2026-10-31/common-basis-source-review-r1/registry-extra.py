from pathlib import Path
import runpy,json
L=Path(__file__).resolve().parent; fetch=runpy.run_path(str(L/'fetch.py'))['fetch']
for repo,tag in [('the-omega-institute/trureturing','omega'),('Vilin97/lean-pool','pool')]:
 h=json.loads(fetch(tag+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD'));sha=h['sha'];t=json.loads(fetch(tag+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1'))
 if t.get('truncated'):
  root=json.loads(fetch(tag+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+sha));paths=[]
  for e in root.get('tree',[]):
   if e['type']=='tree' and e['path'] in ['Problems','D5','preprints']:
    sub=json.loads(fetch(tag+'-sub-'+e['path']+'.json','https://api.github.com/repos/'+repo+'/git/trees/'+e['sha']+'?recursive=1'));paths +=[dict(x,path=e['path']+'/'+x['path']) for x in sub.get('tree',[])];print('complete',e['path'],not sub.get('truncated'),flush=True)
 else:paths=t.get('tree',[])
 (L/(tag+'-paths.json')).write_text(json.dumps(paths))
 for e in paths:
  p=e['path']; low=p.lower()
  if e['type']=='blob' and ((tag=='pool' and (p.startswith('candidates/') or p=='LeanPool/projects.yml')) or (any(w in low for w in ['matroid','lason','332371']) and p.endswith(('.tex','.lean','.md','.yml','.json')))):
   fetch(tag+'--'+p.replace('/','__'),'https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+p)
