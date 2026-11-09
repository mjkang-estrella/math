import pathlib,urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(url,label):
 denied=D/'outputs/denied-hosts.json'; hosts=json.loads(denied.read_text()) if denied.exists() else []
 host=urllib.parse.urlsplit(url).hostname
 if host in hosts:return {'url':url,'status':'skipped denied host'}
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
 p=D/'sources'/f'{label}-{stamp}';p.mkdir()
 class Guard(urllib.request.HTTPRedirectHandler):
  def redirect_request(self,req,fp,code,msg,headers,newurl):
   if urllib.parse.urlsplit(newurl).hostname in hosts:raise RuntimeError('redirect to denied host')
   return super().redirect_request(req,fp,code,msg,headers,newurl)
 r={'url':url,'utc':stamp}
 try:
  res=urllib.request.build_opener(Guard()).open(urllib.request.Request(url,headers={'User-Agent':'Mathematics-research/1.0'}),timeout=25)
  b=res.read();r.update(status=res.status,final_url=res.url,headers=dict(res.headers))
 except urllib.error.HTTPError as e:
  b=e.read();r.update(status=e.code,final_url=e.url,headers=dict(e.headers))
  if e.code in (403,429):hosts.append(urllib.parse.urlsplit(e.url).hostname);denied.write_text(json.dumps(sorted(set(hosts))))
 except Exception as e:b=b'';r.update(status='error',error=str(e))
 (p/'body').write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),body=str(p/'body'))
 (p/'receipt.json').write_text(json.dumps(r,indent=2));return r
if __name__=='__main__':print(json.dumps(fetch(sys.argv[1],sys.argv[2])))
