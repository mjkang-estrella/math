import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1];todo=[];ver={}
for p in (D/'sources').glob('*-abs.html'):
 a=p.name[:-9];s=p.read_text();vs=sorted(set(re.findall(re.escape(a)+r'v(\d+)',s)),key=int);ver[a]=vs
 for v in vs:
  todo.append((a+'v'+v+'.html','https://arxiv.org/html/'+a+'v'+v))
(D/'versions.json').write_text(json.dumps(ver,indent=2));(D/'version-plan.json').write_text(json.dumps(todo))
t=[]
for owner,repo in [('Vilin97','lean-pool'),('openai','math'),('the-omega-institute','trureturing')]:
 o=json.loads((D/'sources'/(owner+'-head.json')).read_text());sha=o.get('sha');print(owner,sha)
 if sha:t.append((owner+'-tree.json',f'https://api.github.com/repos/{owner}/{repo}/git/trees/{sha}?recursive=1'))
(D/'tree-plan.json').write_text(json.dumps(t))
