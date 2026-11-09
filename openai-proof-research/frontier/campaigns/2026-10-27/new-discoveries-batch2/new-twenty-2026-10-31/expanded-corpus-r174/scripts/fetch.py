import urllib.request,urllib.error,urllib.parse,pathlib,json,hashlib,datetime,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
def fetch(url,name):
 denied=set()
 rp=L/'outputs/http.jsonl'
 if rp.exists():
  for l in rp.read_text().splitlines():
   d=json.loads(l)
   if d.get('status') in [403,429]:denied.add(urllib.parse.urlparse(d['final_url']).hostname)
 class Safe(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host blocked')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 d=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=name)
 if urllib.parse.urlparse(url).hostname in denied:
  d.update(status='blocked_inherited_denial',final_url=url);data=None
 else:
  try:
   r=urllib.request.build_opener(Safe).open(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=25)
   data=r.read();d.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(L/name).write_bytes(data)
  except urllib.error.HTTPError as e:d.update(status=e.code,final_url=e.url);data=None
  except Exception as e:d.update(status='error',final_url=url,error=str(e));data=None
 with rp.open('a') as f:f.write(json.dumps(d)+'\n')
 print(json.dumps(d),flush=True)
 return data
if __name__=='__main__':fetch(sys.argv[1],sys.argv[2])
