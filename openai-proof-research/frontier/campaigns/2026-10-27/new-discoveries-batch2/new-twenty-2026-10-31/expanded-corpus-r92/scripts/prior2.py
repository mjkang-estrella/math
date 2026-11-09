from fetch import D,get
import json,urllib.parse
x=json.load(open(D/'sources/comb-openalex.json'))['results'][0]
a=x['authorships'][0]['author']['id'].split('/')[-1]
print(get(('comb-author-later.json','https://api.openalex.org/works?filter=author.id:'+a+',from_publication_date:2026-02-27&per-page=100')))
print(get(('comb-bonato-index.json','https://api.openalex.org/works?search='+urllib.parse.quote('Bounds on the burning numbers of spiders and path-forests')+'&per-page=3')))
for n in ['comb-author-later','comb-bonato-index']:
 p=D/f'sources/{n}.json'
 if p.exists():
  for x in json.load(open(p)).get('results',[]):print(n,x['display_name'],[(z.get('landing_page_url'),z.get('pdf_url')) for z in x.get('locations',[])])
