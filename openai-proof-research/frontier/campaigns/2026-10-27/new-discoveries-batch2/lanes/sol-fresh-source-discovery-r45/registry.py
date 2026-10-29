import pathlib,json,subprocess,hashlib
P=pathlib.Path(__file__).resolve().parent
old=P.parent/'sol-fresh-source-discovery-r44'/'sources'
def fetch(n,u):
 subprocess.run(['python3',str(P/'fetch.py'),n,u],check=True)
 return json.loads((P/'sources'/n).read_text())
out={}
for k,names in [('omega',['omega-D5.json','omega-Problems.json']),('omega-main',['omega-main-tree.json']),('openai',['openai-preprints.json']),('aim',['aim-tree.json']),('count',['count-tree.json'])]:
 h=json.loads((P/'sources'/f'{k}-head.json').read_text())['sha'];out[k]={'head':h}
 if k=='omega' and h!=json.loads((old/f'{k}-head.json').read_text())['sha']:
  d=fetch('delta.json',f'https://api.github.com/repos/the-omega-institute/trureturing/compare/c400e154d065a0d32235cd7cfd28b950fd087315...{h}')
  out[k]['delta']={'commits':d.get('total_commits'),'files':[x['filename'] for x in d.get('files',[])]}
  root=fetch('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')
  for s in ['D5','Problems']:
   sha=next(x['sha'] for x in root['tree'] if x['path']==s)
   fetch(f'omega-{s}.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1')
 for n in names:
  f=P/'sources'/n
  if not f.exists():
   assert h==json.loads((old/f'{k}-head.json').read_text())['sha']
   f.write_bytes((old/n).read_bytes())
  d=json.loads(f.read_text());assert not d.get('truncated')
  matches=[x['path'] for x in d['tree'] if any(t in x['path'].lower() for t in ['dimer','pell','guo-tao','guotao','numericalsemigroup','numerical-semigroup','felconjecture','fel-conjecture'])]
  out[k][n]={'entries':len(d['tree']),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'matches':matches}
 print(k,h,[(n,out[k][n]['entries']) for n in names])
(P/'registry-screen.json').write_text(json.dumps(out,indent=2))
