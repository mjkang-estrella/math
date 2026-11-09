from fetch import get,D
import json,urllib.parse
q='https://api.openalex.org/works?search='+urllib.parse.quote('Burning rooted graph products')+'&per-page=5'
print(get(('comb-openalex.json',q)))
p=D/'sources/comb-openalex.json'
if p.exists():
 d=json.load(open(p));print([(x['id'],x['display_name'],x.get('cited_by_count')) for x in d.get('results',[])])
 for x in d.get('results',[]):
  if x['display_name'].lower()=='burning rooted graph products':
   print(get(('comb-citing-openalex.json','https://api.openalex.org/works?filter=cites:'+x['id'].split('/')[-1]+'&per-page=50')))
