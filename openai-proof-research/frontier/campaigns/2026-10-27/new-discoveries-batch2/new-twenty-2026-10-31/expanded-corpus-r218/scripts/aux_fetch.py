import pathlib,json,runpy,urllib.parse,re
D=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
f('https://raw.githubusercontent.com/networkx/networkx/main/networkx/generators/atlas.dat.gz','atlas-data')
f('https://www.trureturing.org/conjectures.html?lang=en','omega-live-conjectures')
for i in ['374103','374204','374250','374340','374386','374492','374731','374894','374904','375027','375053']:
 p=next(D.glob('http/*-'+i+'-abs-0.body'));title=re.search('<title>.*?] (.*?)</title>',p.read_text()).group(1)
 r=f('https://api.openalex.org/works?search='+urllib.parse.quote(title)+'&per-page=3',i+'-openalex')
 try:
  x=json.loads((D/r['steps'][-1]['file']).read_text())['results']
  for w in x[:1]:
   if w.get('cited_by_count',0):f('https://api.openalex.org/works?filter=cites:'+w['id'].rsplit('/',1)[-1]+'&per-page=100',i+'-citers')
 except Exception:pass
