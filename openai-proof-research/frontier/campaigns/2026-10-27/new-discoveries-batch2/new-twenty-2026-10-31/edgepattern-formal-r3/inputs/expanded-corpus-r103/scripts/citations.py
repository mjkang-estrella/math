from fetch import get,D
import json,urllib.parse
for name,q in [('edge-citers.json','filter=cites:W3215181870&per-page=100'),('edge-prior-search.json','search='+urllib.parse.quote('"convex combination" "Sereni" "pattern"')+'&per-page=20')]:print(get((name,'https://api.openalex.org/works?'+q)),flush=True)
