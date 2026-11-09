from fetch import fetch
import json,urllib.parse,concurrent.futures,pathlib
r=json.load(open('reservation.json'))['rows']
def job(x):
 fetch('https://api.openalex.org/works?search='+urllib.parse.quote(x['title'])+'&per-page=5','prior-'+str(x['mathdb_id'])+'.json')
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as ex:list(ex.map(job,r))
for x in r:
 p=pathlib.Path('sources/prior-'+str(x['mathdb_id'])+'.json')
 if p.exists():
  print(x['mathdb_id'],[(j['title'],j.get('doi'))for j in json.loads(p.read_text()).get('results',[])])
