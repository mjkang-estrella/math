import sys,json,time,urllib.parse
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent));from fetch import D,get,blocked
queries=['"2102.02918" OR "2102.03528" OR "2102.05250" lean','"2103.05814" OR "2103.07047" OR "2104.02930" lean','"2104.08257" OR "2104.12030" OR "2104.12270" lean','"2105.03890" OR "2105.04137" OR "2105.05015" lean','"2106.11720" OR "2106.14042" OR "2107.01397" lean','"2107.06706" OR "2107.13789" OR "2107.14102" lean','carousel OR "Sedlar" OR "coupled choosability" lean','"slow nim" OR "fractional transversal" OR "grid genus" lean']
records=[]
for n,q in enumerate(queries):
 if n:time.sleep(9)
 rec=get(f'github-search-{n+1}.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 records.append({'query':q,**rec})
 if rec.get('status') in (403,429):break
(D/'outputs/github-queries.json').write_text(json.dumps(records,indent=2))
