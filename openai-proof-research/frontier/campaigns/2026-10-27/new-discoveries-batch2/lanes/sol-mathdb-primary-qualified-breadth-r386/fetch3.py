import pathlib,urllib.request,urllib.error,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;(L/'primary').mkdir(exist_ok=True)
jobs=[('firefighter-v1','https://arxiv.org/pdf/2409.14303v1'),('hankel-successor-search','https://export.arxiv.org/api/query?search_query=all:Hankel%20AND%20all:Shallit%26max_results=5'),('kaprekar-successor-search','https://arxiv.org/search/?query=Kaprekar%26searchtype=all%26abstracts=show%26order=-announced_date_first%26size=25')]
for name,url in jobs:
 meta={'url':url,'requested_version':url.rsplit('/',1)[-1],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearchSourceReview/1.0'}),timeout=35) as r:
   b=r.read(8*1024*1024);meta.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
 except urllib.error.HTTPError as e:b=e.read(100000);meta.update(status=e.code,error=str(e),stop_no_retry=True)
 except Exception as e:b=b'';meta.update(error=repr(e),stop_no_retry=True)
 (L/'primary'/f'{name}.body').write_bytes(b);meta.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b));(L/'primary'/f'{name}.meta.json').write_text(json.dumps(meta,indent=2)+'\n');print(name,json.dumps(meta))
