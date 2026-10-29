import pathlib,json,subprocess,hashlib
P=pathlib.Path(__file__).resolve().parent
old=P.parent/'sol-fresh-source-discovery-r43'/'sources'
def fetch(n,u):
 subprocess.run(['python3',str(P/'fetch.py'),n,u],check=True)
 return json.loads((P/'sources'/n).read_text())
report={}
for k in ['omega','omega-main','openai','aim','count']:
 h=json.loads((P/'sources'/f'{k}-head.json').read_text())['sha'];report[k]={'head':h}
 print(k,h)
h=report['omega']['head']
if h==json.loads((old/'omega-head.json').read_text())['sha']:
 names=['omega-D5.json','omega-Problems.json']
else:
 root=fetch('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')
 names=[]
 for s in ['D5','Problems']:
  sha=next(x['sha'] for x in root['tree'] if x['path']==s)
  d=fetch('omega-'+s+'.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1')
  assert not d.get('truncated'); names.append('omega-'+s+'.json')
for k,names in [('omega',names),('omega-main',['omega-main-tree.json']),('openai',['openai-preprints.json']),('aim',['aim-tree.json']),('count',['count-tree.json'])]:
 for name in names:
  src=P/'sources'/name
  if not src.exists():
   assert report[k]['head']==json.loads((old/f'{k}-head.json').read_text())['sha']
   src.write_bytes((old/name).read_bytes())
  d=json.loads(src.read_text());assert not d.get('truncated')
  terms=['koutsch','kratt','schlosser','francesco','logfunction','log-function','lamkin','tkocz','polynomialfactor','polynomial-factor']
  matches=[x['path'] for x in d['tree'] if any(t in x['path'].lower() for t in terms)]
  report[k][name]={'entries':len(d['tree']),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'matches':matches}
  print(name,len(d['tree']),matches)
(P/'registry-screen.json').write_text(json.dumps(report,indent=2))
