import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys,time
D=pathlib.Path(__file__).resolve().parents[1];denied=set();receipts=[]
def fetch(url,name):
 host=urllib.parse.urlparse(url).netloc
 if host in denied:return None
 class Redirect(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlparse(newurl).netloc in denied:raise RuntimeError('denied redirect host')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'mathematics-research/1.0'}),timeout=25) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),file=name);(D/'sources'/name).write_bytes(data)
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429):denied.add(host)
 receipts.append(rec);(D/'outputs'/('fetch-'+sys.argv[1]+'.json')).write_text(json.dumps(receipts,indent=2));return rec
if sys.argv[1]=='sources':
 for a in sorted(set(x['source_url'].split('/')[-1] for x in json.loads((D/'extracted.json').read_text()).values())):
  fetch('https://arxiv.org/html/'+a,'arxiv-'+a+'.html')
elif sys.argv[1]=='heads':
 for repo in ['Vilin97/lean-pool','the-omega-institute/trureturing','openai/math']:
  rec=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',repo.replace('/','-')+'-head.json')
  if rec and rec.get('status')==200:
   sha=json.loads((D/'sources'/rec['file']).read_text())['sha'];fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1',repo.replace('/','-')+'-tree.json')
