from retrieve import L,fetch
import json,urllib.parse
j=json.loads((L/'sources/openalex-juras.json').read_text())
for x in j['results']:
 print(x['id'],x['title'],x.get('doi'),x.get('cited_by_count'))
 if x['title'].lower()=='on commuting probabilities in finite groups and rings':
  wid=x['id'].split('/')[-1]
  fetch('https://api.openalex.org/works?'+urllib.parse.urlencode({'filter':'cites:'+wid,'per-page':30}),'juras-citers.json')
  if (L/'sources/juras-citers.json').exists():
   for c in json.loads((L/'sources/juras-citers.json').read_text())['results']:print('CITER',c['title'],c.get('doi'),c.get('best_oa_location'))
