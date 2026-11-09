import pathlib,urllib.request,urllib.error,urllib.parse,json,datetime,hashlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def get(key,url):
 p=D/'sources'/key
 if p.exists() or p.with_suffix(p.suffix+'.receipt.json').exists(): raise RuntimeError('receipt exists '+key)
 deny=D/'outputs/denied-hosts.json'; blocked=json.loads(deny.read_text()) if deny.exists() else []
 class Redirect(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlparse(newurl).hostname in blocked: raise RuntimeError('redirect to denied host')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in blocked:raise RuntimeError('denied host; skipped')
  with urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=25) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
 except urllib.error.HTTPError as e:
  data=e.read();p.write_bytes(data);rec.update(status=e.code,sha256=hashlib.sha256(data).hexdigest(),error=str(e))
  if e.code in (403,429):
   blocked.append(urllib.parse.urlparse(e.url).hostname);deny.write_text(json.dumps(blocked))
 except Exception as e:rec['error']=str(e)
 p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status'),rec.get('error',''),flush=True)
 return rec
if __name__=='__main__':
 if sys.argv[1]=='initial':
  for key,repo in [('pool','Vilin97/lean-pool'),('omega','the-omega-institute/trureturing'),('openai','openai/math')]:get(key+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
  x=json.loads((D/'extracted.json').read_text());urls=list(dict.fromkeys(o['source_url'] for o in x.values()))
  for url in urls:get(url.rsplit('/',1)[-1]+'-abs.html',url)
 else:get(sys.argv[1],sys.argv[2])
