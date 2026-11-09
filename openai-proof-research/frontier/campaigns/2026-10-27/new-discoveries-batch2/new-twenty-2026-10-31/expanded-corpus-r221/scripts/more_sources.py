import pathlib,json,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
for a in sorted({o['source_url'].rsplit('/',1)[-1] for o in json.loads((D/'extracted.json').read_text()).values()}):get(a+'-abs.html','https://arxiv.org/abs/'+a)
get('fox-tidor.html','https://drops.dagstuhl.de/storage/00lipics/lipics-vol367-socg2026/LIPIcs.SoCG.2026.50/LIPIcs.SoCG.2026.50.html')
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 t=json.loads((D/f'sources/{key}-tree.json').read_text());print(key,'truncated',t.get('truncated'))
 for p in ['D5','Problems','preprints']:
  x=next((x for x in t.get('tree',[]) if x['path']==p),None)
  if x:get(key+'-'+p+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/'+x['sha']+'?recursive=1')
