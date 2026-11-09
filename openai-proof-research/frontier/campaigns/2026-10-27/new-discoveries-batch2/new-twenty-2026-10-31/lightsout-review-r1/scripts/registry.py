import json,subprocess,sys,resource,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
r=Path(__file__).resolve().parents[1]
for n,repo,wanted in [('openai','openai/math',['preprints']),('omega','the-omega-institute/trureturing',['Problems','D5'])]:
 head=json.loads((r/f'sources/{n}-head.json').read_text());sha=head['commit']['tree']['sha']
 subprocess.run([sys.executable,str(r/'scripts/fetch.py'),f'{n}-root.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}'],timeout=30)
 p=r/f'sources/{n}-root.json'
 if not p.exists():continue
 for entry in json.loads(p.read_text()).get('tree',[]):
  if entry['path'] in wanted:
   name=f'{n}-{entry["path"]}.json';subprocess.run([sys.executable,str(r/'scripts/fetch.py'),name,f'https://api.github.com/repos/{repo}/git/trees/{entry["sha"]}?recursive=1'],timeout=30)
   p=r/'sources'/name
   if p.exists():
    d=json.loads(p.read_text());hits=[x for x in d.get('tree',[]) if any(k in x['path'].lower() for k in ['lights','automata','chebyshev','353680','nullity','grid'])];(r/'logs'/(name+'.screen.json')).write_text(json.dumps({'head':head['sha'],'truncated':d.get('truncated'),'entries':len(d.get('tree',[])),'hits':hits},indent=2));print(n,entry['path'],len(d.get('tree',[])),d.get('truncated'),len(hits))
