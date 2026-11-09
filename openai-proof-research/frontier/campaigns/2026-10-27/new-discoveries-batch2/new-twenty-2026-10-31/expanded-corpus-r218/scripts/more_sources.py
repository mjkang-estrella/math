import runpy,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(D/'scripts/fetch.py'))['fetch']
urls=[('signed-prior','https://arxiv.org/pdf/1502.04561'),('tbsym-prior','https://ideosphere.ai/papers/tbsym-graphs')]
for i,a in [('373859','2603.25116'),('374103','2604.07104'),('374250','2604.16759'),('374480','2604.27615'),('374731','2605.14402')]:urls.append((i+'-v1','https://arxiv.org/pdf/'+a+'v1'))
sha=json.loads(next(D.glob('http/*trureturing-head-0.body')).read_text())[0]['sha']
for p in ['D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.lean','Blueprint/D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.md','conjectures.html']:
 urls.append(('omega-'+pathlib.Path(p).name,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+sha+'/'+p))
for label,url in urls:f(url,label)
