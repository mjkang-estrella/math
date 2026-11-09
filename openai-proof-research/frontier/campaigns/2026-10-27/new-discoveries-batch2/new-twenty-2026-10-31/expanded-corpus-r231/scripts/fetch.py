import pathlib,urllib.request,urllib.error,json,datetime,hashlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
state=D/'sources/denied.json'
denied=set(json.loads(state.read_text())) if state.exists() else set()
opener=urllib.request.build_opener(NoRedirect)
def fetch(key,url):
 host=urllib.parse.urlparse(url).hostname
 p=D/'sources'/key; receipt=p.with_name(p.name+'.receipt.json')
 if receipt.exists():return
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if host in denied: rec['skipped']='host previously denied'
 else:
  try:
   with opener.open(urllib.request.Request(url,headers={'User-Agent':'Research verification (public mathematical literature)'}),timeout=18) as r:
    data=r.read(20000000);rec.update(status=r.status,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());p.write_bytes(data)
   if b'captcha' in data[:10000].lower() or b'bot challenge' in data[:10000].lower():denied.add(host);rec['challenge']=True
  except Exception as e:
   rec['error']=str(e)
   if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):denied.add(host)
 receipt.write_text(json.dumps(rec,indent=2)+'\n');state.write_text(json.dumps(sorted(denied))+'\n');print(key,rec.get('status',rec.get('error',rec.get('skipped'))),flush=True)
if __name__=='__main__':
 for key,url in json.loads(pathlib.Path(sys.argv[1]).read_text()):fetch(key,url)
