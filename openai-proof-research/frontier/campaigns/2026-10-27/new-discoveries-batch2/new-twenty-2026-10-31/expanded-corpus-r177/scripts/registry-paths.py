import pathlib,json,re,sys
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'outputs/registry-screen.json').read_text());matches=[];todo=[]
terms=['pinnacle','gessel','zhuang','brimkov','crupi','ficarra','frustrat','morita','larman','binariz','forking','internal.partition','two.eigen','cover.ideal','joints']
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json']:
 o=json.loads(p.read_text())
 for t in o.get('tree',[]):
  if any(re.search(s,t['path'],re.I) for s in terms):
   matches.append({'tree':p.name,**t})
   if t['type']=='blob' and ('pinnacle' in t['path'].lower() or 'cover' in t['path'].lower()):todo.append(['omega-body-'+str(len(todo))+'.txt',f"https://raw.githubusercontent.com/the-omega-institute/trureturing/{r['heads']['omega']}/"+p.stem.removeprefix('omega-')+'/'+t['path']])
r['parsed_omega_path_matches']=matches;(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2));(D/'outputs/omega-matches-plan.json').write_text(json.dumps(todo));print(json.dumps(matches,indent=2)[:7500])
