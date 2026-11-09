import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]; receipts=[];denied=set()
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect())
def fetch(url,name):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied:raise RuntimeError('host previously denied')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=18) as f:b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/name).write_bytes(b)
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   r['status']=e.code
   if e.code in [403,429]:denied.add(urllib.parse.urlparse(e.url).hostname)
 receipts.append(r);(D/'outputs'/('fetch-'+sys.argv[1]+'.json')).write_text(json.dumps(receipts,indent=2));print(name,r.get('status',r.get('error')),flush=True)
 return r
if sys.argv[1]=='sources':
 for i,o in json.loads((D/'extracted.json').read_text()).items():fetch(o['source_url'].replace('/abs/','/pdf/'),i+'.pdf')
else:
 for repo,key in [('Vilin97/lean-pool','pool'),('the-omega-institute/trureturing','omega'),('openai/math','openai')]:
  r=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',key+'-head.json')
  if r.get('status')==200:
   sha=json.loads((D/'sources'/(key+'-head.json')).read_text())['sha']
   fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha+'?recursive=1',key+'-tree.json')
   if key=='pool':fetch('https://raw.githubusercontent.com/'+repo+'/'+sha+'/projects.yml','pool-projects.yml')
