import pathlib,json,runpy,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];fetch=runpy.run_path(str(D/'scripts/fetch.py'))['fetch'];screen=json.loads((D/'outputs/registry-screen.json').read_text())
for repo,parts in [('the-omega-institute/trureturing',['D5','Problems']),('openai/math',['preprints'])]:
 sha=screen[repo]['head'];tag=repo.split('/')[-1];b=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,'sources/'+tag+'-root.json')
 if not b:continue
 tree=json.loads(b)['tree']
 for part in parts:
  match=next((p for p in tree if p['path']==part),None)
  if match:
   fetch('https://api.github.com/repos/'+repo+'/git/trees/'+match['sha']+'?recursive=1','sources/'+tag+'-'+part+'-tree.json')
xs=json.loads((D/'extracted.json').read_text());scopes=[]
for p in (D/'sources').glob('*-tree.json'):
 data=json.loads(p.read_text());paths=[x['path'] for x in data.get('tree',[])];hits={}
 for i,x in xs.items():
  words=[i,x['source_url'].split('/')[-1]]
  hits[i]=[q for q in paths if any(w.lower() in q.lower() for w in words)]
 scopes.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':data.get('truncated'),'path_count':len(paths),'exact_id_hits':hits})
screen['current_path_scopes']=scopes;screen['tree_limit']='Exact identifier path searches only; semantic keyword scan separately recorded. A path non-hit does not clear theorem bodies.'
(D/'outputs/registry-screen.json').write_text(json.dumps(screen,indent=2,ensure_ascii=False))
