from pathlib import Path
import requests,json,hashlib,datetime
L=Path(__file__).resolve().parent
urls=[('arxiv-current','https://export.arxiv.org/api/query?search_query=all:%22monochromatic%22+AND+all:%22Schur%22&start=0&max_results=30'),('author-primary','https://www.koutschan.de/publ/'),('registry-current','https://api.github.com/repos/teorth/equational_theories')]
# GitHub API is a known denied route and is deliberately never requested.
rows=[]
for name,url in urls[:2]:
 try:
  r=requests.get(url,timeout=25,allow_redirects=False); data=r.content
  p=L/(name+'.body');p.write_bytes(data)
  rows.append(dict(url=url,status=r.status_code,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),file=p.name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),redirect=r.headers.get('Location')))
 except Exception as e:rows.append(dict(url=url,error=str(e)))
(L/'retrieval.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
