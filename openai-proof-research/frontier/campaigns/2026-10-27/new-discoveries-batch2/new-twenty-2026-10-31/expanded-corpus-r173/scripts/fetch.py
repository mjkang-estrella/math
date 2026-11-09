import pathlib,json,urllib.request,urllib.error,hashlib,datetime,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(url,name):
 receipts=D/'outputs/http.jsonl'; denied=D/'outputs/denied.json'
 hosts=json.loads(denied.read_text()) if denied.exists() else []
 class Guard(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlparse(newurl).hostname in hosts: raise RuntimeError('denied redirect host')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 host=urllib.parse.urlparse(url).hostname
 if host in hosts: return None
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.build_opener(Guard()).open(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=25) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/name).write_bytes(b)
 except Exception as e:
  r.update(error=str(e),status=getattr(e,'code',None))
  if getattr(e,'code',None) in (403,429):hosts.append(host);denied.write_text(json.dumps(hosts))
  b=None
 with receipts.open('a') as f:f.write(json.dumps(r)+'\n')
 print(url,r.get('status'),r.get('bytes'),flush=True)
 return b
if __name__=='__main__':
 if sys.argv[1]=='sources':
  for a in sorted({x['source_url'].split('/')[-1] for x in json.loads((D/'extracted.json').read_text()).values()}):
   fetch('https://arxiv.org/abs/'+a,'sources/'+a+'-abs.html')
   fetch('https://arxiv.org/html/'+a,'sources/'+a+'.html')
 elif sys.argv[1]=='registry':
  out={}
  for repo in ['Vilin97/lean-pool','the-omega-institute/trureturing','openai/math']:
   name=repo.split('/')[-1];b=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD','sources/'+name+'-head.json')
   if b:
    s=json.loads(b)['sha'];out[repo]={'head':s}
    if name=='lean-pool':
     fetch('https://raw.githubusercontent.com/'+repo+'/'+s+'/projects.yml','sources/lean-pool-projects.yml')
     tr=fetch('https://api.github.com/repos/'+repo+'/git/trees/'+s+'?recursive=1','sources/lean-pool-tree.json')
     if tr:
      for p in json.loads(tr)['tree']:
       if p['path'].startswith('candidates/') and p['type']=='blob':fetch('https://raw.githubusercontent.com/'+repo+'/'+s+'/'+p['path'],'sources/pool-'+p['path'].replace('/','_'))
  (D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
 else:fetch(sys.argv[1],sys.argv[2])
