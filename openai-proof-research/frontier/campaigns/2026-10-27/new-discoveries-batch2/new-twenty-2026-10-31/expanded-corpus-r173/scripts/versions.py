import pathlib,runpy,re,json
D=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(D/'scripts/fetch.py'))['fetch'];out={}
for p in (D/'sources').glob('*-abs.txt'):
 a=p.name.split('-')[0];v=re.findall(r'\[v(\d+)\]',p.read_text());out[a]=v
 if len(v)>1:
  for k in v:f('https://arxiv.org/html/'+a+'v'+k,'sources/'+a+'v'+k+'.html')
(D/'outputs/arxiv-versions.json').write_text(json.dumps(out,indent=2))
