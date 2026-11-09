from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,xml.etree.ElementTree as ET
L=Path(__file__).resolve().parent
queries=[('crossref-author','https://api.crossref.org/works?rows=10&query.author=Chapman%20McGuire&query.title=twisted%20trace%20curves'),('citing','https://api.openalex.org/works?filter=cites:W3128157356&per-page=20'),('arxiv-focused','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('au:McGuire AND (all:trace OR all:Fibonacci)')+'&max_results=20'),('ucd','https://maths.ucd.ie/~gmg/'),('exeter','https://empslocal.ex.ac.uk/people/staff/rjchapma/papers/trace.pdf')]
# Last route omitted: no observed locator for a PDF; do not guess primary body URLs.
queries=queries[:-1]
records=[]
for name,url in queries:
 rec=dict(name=name,url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=20) as r:
   data=r.read(4000001);assert len(data)<=4000000
   rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(L/'retrieved'/name).write_bytes(data)
 except Exception as e:rec['error']=str(e)
 records.append(rec);print(json.dumps(rec),flush=True)
(L/'followup-retrieval.json').write_text(json.dumps(records,indent=2)+'\n')
for name in ['arxiv-search','arxiv-focused']:
 p=L/'retrieved'/name
 if p.exists():
  root=ET.fromstring(p.read_bytes());ns={'a':'http://www.w3.org/2005/Atom'}
  print(name,json.dumps([{'id':e.findtext('a:id',namespaces=ns),'title':e.findtext('a:title',namespaces=ns),'published':e.findtext('a:published',namespaces=ns)} for e in root.findall('a:entry',ns)]))
p=L/'retrieved/crossref-author'
if p.exists():print('crossref-author',json.dumps([{'title':e.get('title'),'doi':e.get('DOI')} for e in json.loads(p.read_text())['message']['items']]))
print('source-comparison',(L/'source-comparison.json').read_text())
