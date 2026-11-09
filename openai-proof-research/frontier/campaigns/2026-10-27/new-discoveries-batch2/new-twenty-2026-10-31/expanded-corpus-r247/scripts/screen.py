import pathlib,json,re,hashlib,urllib.parse
L=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((L/'reservation.json').read_text())['rows'];o={'heads':{},'index_hits':{},'tree_hits':{}};q=[]
for name,repo in [('openai','openai/math'),('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing')]:
 h=json.loads((L/'http'/f'{name}-head/body').read_text())['sha'];t=json.loads((L/'http'/f'{name}-tree/body').read_text());o['heads'][name]={'sha':h,'truncated':t.get('truncated')}
 pats=['leverage','randic','randić','mountain','sierpinski','laver','sullivan','schubert','diamond','eulerian','nef','punctured','kontsevich','cube','antimagic']+[str(r['mathdb_id']) for r in rs]
 o['tree_hits'][name]=[x['path'] for x in t['tree'] if any(p in x['path'].lower() for p in pats)]
 if name=='openai':
  for p in ['README.md','CONTENTS.md']:q.append(('openai-raw-'+p,f'https://raw.githubusercontent.com/{repo}/{h}/{p}'))
for p in (L/'http').glob('poolraw-*/body'):
 s=p.read_text(); hits=[]
 for n,line in enumerate(s.splitlines(),1):
  if any(p in line.lower() for p in pats):hits.append({'line':n,'text':line})
 o['index_hits'][p.parent.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'hits':hits}
for name,term in [('leverage','"leverage centrality" lean'),('randic','"randic" lean'),('packing','"anchored rectangles" lean'),('laver','"Laver" lean')]:q.append(('github-search-'+name,'https://api.github.com/search/repositories?q='+urllib.parse.quote(term)))
for a in ['2603.20104','2604.24932','2511.16919','2610.38727']:q.extend([(a+'-abs','https://arxiv.org/abs/'+a),(a+'-pdf','https://arxiv.org/pdf/'+a)])
q.extend([('dowlin','https://www.ams.org/journals/jams/2024-37-04/S0894-0347-2024-01039-0/'),('probxiv-cube','https://probxiv.com/problems/the-largest-projective-cube-free-subsets-of-mathbb-z-2-n-2')])
(L/'registry-screen.json').write_text(json.dumps(o,indent=2));(L/'followupqueue.json').write_text(json.dumps(q)); print(json.dumps(o['heads']));print(json.dumps(o['tree_hits'],indent=2)[:8000])
