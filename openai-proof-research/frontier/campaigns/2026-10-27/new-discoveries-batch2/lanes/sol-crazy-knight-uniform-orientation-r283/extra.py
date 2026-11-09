import pathlib,urllib.request,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
url='https://export.arxiv.org/api/query?search_query=au:Pasotti_AND_%28all:tour_OR_all:diagonal%29&start=0&max_results=40&sortBy=submittedDate&sortOrder=descending'
rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as f:b=f.read(2000000);rec.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 (L/'author-successors.xml').write_bytes(b)
 assert hashlib.sha256((L/'author-successors.xml').read_bytes()).hexdigest()==rec['sha256']
except Exception as e:rec['failure']=str(e)
(L/'extra-access.json').write_text(json.dumps(rec,indent=2)+'\n')
print(rec)
