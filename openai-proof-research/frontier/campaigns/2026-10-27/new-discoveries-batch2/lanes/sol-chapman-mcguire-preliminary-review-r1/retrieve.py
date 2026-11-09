from pathlib import Path
import urllib.request,urllib.parse,json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent;(L/'retrieved').mkdir(exist_ok=True)
queries=[('arxiv-abs','https://arxiv.org/abs/2102.02081'),('arxiv-v1','https://arxiv.org/pdf/2102.02081v1'),('crossref','https://api.crossref.org/works?rows=5&query.title='+urllib.parse.quote('On a Family of Twisted Trace Curves over Finite Fields and Fibonacci Numbers')),('openalex','https://api.openalex.org/works?per-page=5&search='+urllib.parse.quote('On a Family of Twisted Trace Curves over Finite Fields and Fibonacci Numbers')),('arxiv-search','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('all:"twisted trace"')+'&max_results=10')]
records=[]
for name,url in queries:
 rec=dict(name=name,url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-review/1.0'}),timeout=20) as r:
   data=r.read(12000001);assert len(data)<=12000000
   rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
   (L/'retrieved'/name).write_bytes(data)
 except Exception as e:rec['error']=str(e)
 records.append(rec);print(json.dumps(rec),flush=True)
(L/'retrieval.json').write_text(json.dumps(records,indent=2)+'\n')
if (L/'retrieved/arxiv-v1').exists():
 subprocess.run(['pdftotext','-layout',str(L/'retrieved/arxiv-v1'),str(L/'retrieved/arxiv-v1.txt')],check=True)
 a=(L/'retrieved/arxiv-v1.txt').read_bytes();b=(L/'scientific/sources/2102.02081v1.txt').read_bytes()
 (L/'source-comparison.json').write_text(json.dumps({'pdf_equal':(L/'retrieved/arxiv-v1').read_bytes()==(L/'scientific/sources/2102.02081v1.pdf').read_bytes(),'text_equal':a==b,'fresh_text_sha256':hashlib.sha256(a).hexdigest(),'frozen_text_sha256':hashlib.sha256(b).hexdigest()},indent=2)+'\n')
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/n).read_text());print(n,{k:v for k,v in d.items() if isinstance(v,(str,int))},'accepted',len(d.get('accepted',[])))
