from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime
L=Path(__file__).resolve().parent
queries=[('arxiv-citers','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'all:"Borisov" AND (all:"nilpotent" OR all:"polynomial maps")','max_results':15})),('arxiv-zeroloci','https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':'(all:"Schur" AND all:"polynomial" AND all:"primes") OR (all:"arithmetic Nullstellensatz")','max_results':12})),('openalex-citers','https://api.openalex.org/works?'+urllib.parse.urlencode({'search':'Iterations of Integer Polynomial Maps Modulo Primes','per-page':3}))]
receipts=[]
for name,url in queries:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=35) as f:
   data=f.read(3000000);r.update(status=f.status,final_url=f.url)
  q=L/'retrieved'/name;q.parent.mkdir(exist_ok=True);q.write_bytes(data);r.update(path=str(q.relative_to(L)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),frozen_before_read=True)
 except Exception as e:r.update(error=str(e),stop_no_retry=True)
 receipts.append(r)
(L/'retrieval.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))
