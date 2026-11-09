import pathlib,sys,json,urllib.request,urllib.error,urllib.parse,datetime,hashlib,time
D=pathlib.Path(__file__).resolve().parents[1]
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlsplit(newurl).hostname in denied:raise RuntimeError('denied redirect host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
denied=set(json.loads((D/'outputs/denied.json').read_text())) if (D/'outputs/denied.json').exists() else set()
def get(key,url):
 if urllib.parse.urlsplit(url).hostname in denied:return {'skipped':url,'reason':'host previously denied'}
 p=D/'sources'/key;p.mkdir(exist_ok=False)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.build_opener(Guard()).open(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=25) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers));(p/'body').write_bytes(b)
 except urllib.error.HTTPError as e:
  b=e.read();(p/'body').write_bytes(b);rec.update(status=e.code,headers=dict(e.headers),error=str(e))
  if e.code in (403,429):denied.add(urllib.parse.urlsplit(url).hostname)
 except Exception as e:b=b'';rec['error']=str(e)
 rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/'receipt.json').write_text(json.dumps(rec,indent=2));(D/'outputs/denied.json').write_text(json.dumps(sorted(denied)));print(key,rec.get('status',rec.get('error')),len(b),flush=True);return rec
if __name__=='__main__':
 if sys.argv[1]=='initial':
  for repo,key in [('Vilin97/lean-pool','pool'),('openai/math','openai'),('the-omega-institute/trureturing','omega')]:get(key+'-head','https://api.github.com/repos/'+repo+'/commits/HEAD')
  for o in json.loads((D/'extracted.json').read_text()).values():
   a=o['source_url'].rsplit('/',1)[-1]
   if not (D/'sources'/('abs-'+a)).exists():get('abs-'+a,'https://arxiv.org/abs/'+a)
 else:get(sys.argv[1],sys.argv[2])
