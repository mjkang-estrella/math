from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def fetch(name,url):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),name=name)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=22) as r:
   data=r.read(9000001);rec.update(status=r.status,final_url=r.url)
  assert len(data)<=9000000,'size cap';p.write_bytes(data);p.chmod(0o444);rec.update(sha256=hashlib.sha256(data).hexdigest(),size=len(data))
  if data.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True);p.with_suffix('.txt').chmod(0o444);rec['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e:rec['error']=str(e)
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec),flush=True)
if __name__=='__main__':
 if sys.argv[1]=='search':
  q='cat:math.CO AND (ti:conjecture OR ti:questions) AND submittedDate:[200501010000 TO 201712312359]'
  fetch('original-search.xml','https://export.arxiv.org/api/query?'+urllib.parse.urlencode(dict(search_query=q,start=0,max_results=35,sortBy='submittedDate',sortOrder='descending')))
 else:fetch(*sys.argv[1:])
