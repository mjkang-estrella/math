from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime
P=Path(__file__).parent; (P/'live').mkdir(exist_ok=True)
urls=[('arxiv-current','https://arxiv.org/abs/2601.12574'),('bing-exact','https://www.bing.com/search?q='+urllib.parse.quote('"L(3,2,1)" "circulants" "Holub"')),('bing-endpoint','https://www.bing.com/search?q='+urllib.parse.quote('"C_n(1,5)" "labeling" "14"')),('bing-registry','https://www.bing.com/search?q='+urllib.parse.quote('"2601.12574" proof Lean conjecture'))]
records=[]
for name,url in urls:
 r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-review/1.0'}),timeout=25) as f:
   b=f.read(6000000);r.update(status=f.status,effective_url=f.url,content_type=f.headers.get('content-type'))
 except urllib.error.HTTPError as e:b=e.read();r.update(status=e.code,error=str(e))
 except Exception as e:b=b'';r.update(error=str(e))
 (P/'live'/name).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 r['blocked']=r.get('status') in [403,429] or any(s in b.lower() for s in [b'captcha',b'verify you are human',b'just a moment'])
 records.append(r); (P/'live/provenance.json').write_text(json.dumps(records,indent=2)+'\n');print(name,r.get('status'),r['blocked'],len(b),flush=True)
 if r['blocked']:break
