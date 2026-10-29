import json,pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent
def fetch(n,u):
 subprocess.run(['python3',str(P/'fetch.py'),n,u],check=True)
 return json.loads((P/'sources'/n).read_text())
for k,r,b in [('omega','the-omega-institute/trureturing','dev'),('omega-main','the-omega-institute/trureturing','main'),('openai','openai/math','main'),('aim','MColbrook/AIM','main'),('count','suvrit/count-ex-machina','main')]:
 fetch(k+'-head.json',f'https://api.github.com/repos/{r}/commits/{b}')
h=json.loads((P/'sources/omega-head.json').read_text())['sha']
r=fetch('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}')
for s in ['D5','Problems']:
 sha=next(x['sha'] for x in r['tree'] if x['path']==s)
 d=fetch('omega-'+s+'.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}?recursive=1')
 assert not d.get('truncated')
 print(s,len(d['tree']))
 for x in d['tree']:
  if any(t in x['path'].lower() for t in ['sombor','movahedi','diminished']):print('MATCH',s,x)
