import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];out={};todo=[]
patterns=r'isolation|happy|parking|zagreb|temperley|corona|fibonacci|cruick|gleeful|speyer|turanable|raspaud|shattering|rigidity|swapping'
for owner,repo in [('Vilin97','lean-pool'),('openai','math'),('the-omega-institute','trureturing')]:
 p=D/'sources'/(owner+'-tree.json')
 if not p.exists():continue
 o=json.loads(p.read_text());matches=[e for e in o.get('tree',[]) if re.search(patterns,e['path'],re.I)];out[owner]={'truncated':o.get('truncated'),'entries':len(o.get('tree',[])),'matches':matches}
 if owner=='Vilin97':
  sha=json.loads((D/'sources'/(owner+'-head.json')).read_text())['sha']
  for e in o.get('tree',[]):
   if e['path'].endswith('.lean'):todo.append(('pool-'+e['path'].replace('/','_'),f'https://raw.githubusercontent.com/{owner}/{repo}/{sha}/'+e['path']))
(D/'registry-screen.json').write_text(json.dumps(out,indent=2));(D/'pool-plan.json').write_text(json.dumps(todo))
print(json.dumps({k:{'entries':v['entries'],'truncated':v['truncated'],'matches':[e['path'] for e in v['matches']]} for k,v in out.items()},indent=2));print('pool files',len(todo))
