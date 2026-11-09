import pathlib,json,hashlib,datetime,urllib.request,urllib.error,urllib.parse,sys
D=pathlib.Path(__file__).resolve().parents[1]
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**k):return None
opener=urllib.request.build_opener(NoRedirect)
def get(key,url):
 p=D/'sources'/key
 if p.exists() or p.with_name(p.name+'.receipt.json').exists():raise RuntimeError('immutable receipt collision '+key)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=25) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p.write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p))
 except urllib.error.HTTPError as e:
  data=e.read();p.write_bytes(data);rec.update(status=e.code,headers=dict(e.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:rec['error']=str(e)
 p.with_name(p.name+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status',rec.get('error')),rec.get('bytes'),flush=True)
if __name__=='__main__':
 if len(sys.argv)>1:get(sys.argv[1],sys.argv[2])
 else:
  for o in json.loads((D/'extracted.json').read_text()).values():
   url=o['source_url'];a=url.rsplit('/',1)[-1]
   get(a+'.html',url if 'arxiv' not in url else 'https://arxiv.org/html/'+a)
  for key,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
