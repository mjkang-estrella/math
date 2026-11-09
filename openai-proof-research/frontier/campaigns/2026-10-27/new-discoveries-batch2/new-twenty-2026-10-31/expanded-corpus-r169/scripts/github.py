exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(__import__('pathlib').Path(__file__).parent/'fetch.py'),'exec'))
import time
queries=['lean "inversion diameter"','lean "conflict free"','lean "Cameron" "fort"','lean "1710.01710"','lean "precoloring"','lean "Cambrian"','lean "1605.06216"','lean "containment" "robber"']
for j,q in enumerate(queries):
 if j:time.sleep(8)
 r=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-query-'+str(j)+'.json')
 r['query']=q
 (D/'outputs/fetch-github.json').write_text(json.dumps(receipts,indent=2))
 if r.get('status') in [403,429]:break
