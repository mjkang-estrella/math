from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime
P=Path(__file__).parent;records=[]
urls=[('arxiv-radio-title','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"New results on radio k-labelings of distance graphs"')+'&max_results=5'),('arxiv-square-title','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('ti:"L(3,2,1)-labeling of the square of cycles"')+'&max_results=5')]
for name,url in urls:
 r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-review/1.0'}),timeout=25) as f:b=f.read(6000000);r.update(status=f.status,effective_url=f.url,content_type=f.headers.get('content-type'))
 except urllib.error.HTTPError as e:b=e.read();r.update(status=e.code,error=str(e))
 except Exception as e:b=b'';r.update(error=str(e))
 (P/'live'/name).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());r['blocked']=r.get('status') in [403,429] or any(s in b.lower() for s in [b'captcha',b'verify you are human',b'just a moment'])
 records.append(r);(P/'live/provenance3.json').write_text(json.dumps(records,indent=2)+'\n');print(name,r.get('status'),r['blocked'],len(b),flush=True)
 if r['blocked']:break
