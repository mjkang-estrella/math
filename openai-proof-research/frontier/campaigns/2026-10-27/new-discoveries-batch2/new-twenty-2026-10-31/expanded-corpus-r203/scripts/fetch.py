import pathlib,json,hashlib,urllib.request,urllib.error,datetime,sys,time
D=pathlib.Path(sys.argv[1]).resolve(); denied=set()
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Guard())
def fetch(url,label):
 host=urllib.parse.urlparse(url).hostname
 if host in denied:return None
 folder=D/'sources'/label;folder.mkdir(parents=True,exist_ok=False)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'MathematicsResearch/1.0'}),timeout=25) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers));(folder/'body').write_bytes(b);rec['sha256']=hashlib.sha256(b).hexdigest()
 except urllib.error.HTTPError as e:
  b=e.read();(folder/'body').write_bytes(b);rec.update(status=e.code,sha256=hashlib.sha256(b).hexdigest());
  if e.code in (403,429):denied.add(host)
 except Exception as e:rec['error']=str(e)
 (folder/'receipt.json').write_text(json.dumps(rec,indent=2));print(label,rec.get('status',rec.get('error')),flush=True)
 return json.loads(b) if rec.get('status')==200 and 'api.github.com' in url else None
if len(sys.argv)>2 and sys.argv[2]=='sources':
 for i,o in json.loads((D/'extracted.json').read_text()).items():fetch(o['source_url'],'abs-'+i)
if len(sys.argv)>2 and sys.argv[2]=='registry':
 for repo in ['Vilin97/lean-pool','openai/math','the-omega-institute/trureturing']:
  x=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',repo.replace('/','-')+'-head')
  if x:fetch('https://api.github.com/repos/'+repo+'/git/trees/'+x['sha']+'?recursive=1',repo.replace('/','-')+'-tree')
