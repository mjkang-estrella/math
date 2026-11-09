import sys,pathlib,json,re
exec((pathlib.Path(__file__).parent/'fetch.py').read_text())
if mode=='versions':
 for row in json.loads((D/'reservation.json').read_text())['rows']:
  a=row['source_url'].rsplit('/',1)[1];s=(D/'sources'/f'{a}-abs.html').read_text()
  for v in sorted(set(re.findall(r'\[v(\d+)\]',s))):
   name=a+'v'+v+'-body.html'
   if not (D/'sources'/name).exists():get('https://arxiv.org/html/'+a+'v'+v,name)
