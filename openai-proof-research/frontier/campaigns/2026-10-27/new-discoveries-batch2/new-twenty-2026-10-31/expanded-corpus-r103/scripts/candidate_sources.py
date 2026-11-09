from fetch import get,D
import urllib.parse,json
items=[('1904.05618-abs.html','https://arxiv.org/abs/1904.05618'),('edge-openalex.json','https://api.openalex.org/works?search='+urllib.parse.quote('"edge-rooted" "Pirot"')+'&per-page=10'),('1904.05618v1.pdf','https://arxiv.org/pdf/1904.05618v1')]
for x in items:print(get(x),flush=True)
