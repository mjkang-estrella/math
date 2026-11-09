from pathlib import Path
import urllib.request,urllib.error,datetime,json,hashlib,sys
R=Path(__file__).resolve().parent;D=R/'http';D.mkdir(exist_ok=True)
class SafeRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if any(s in newurl.lower() for s in ['google','github','sciencedirect','mathdb']):raise ValueError('barred redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
urllib.request.install_opener(urllib.request.build_opener(SafeRedirect))
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 assert not (D/(name+'.meta.json')).exists(),'no retries'
 assert not any(s in url.lower() for s in ['google','github','sciencedirect','mathdb'])
 t=datetime.datetime.now(datetime.timezone.utc).isoformat(); b=b'';status=None;err=None;final=url;headers={}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Academic source review (public documents)'}),timeout=30) as f:status=f.status;final=f.url;headers=dict(f.headers);b=f.read(15000000)
 except urllib.error.HTTPError as e:status=e.code;b=e.read();err=str(e)
 except Exception as e:err=repr(e)
 p=D/(name+'.body');p.write_bytes(b)
 challenge=any(s in b.lower() for s in [b'incapsula',b'distil_referrer',b'cf-chl-',b'captcha',b'just a moment...',b'verify you are human',b'access denied'])
 m={'url':url,'effective_url':final,'utc':t,'status':status,'headers':headers,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'error':err,'challenge':challenge,'usable':status==200 and not challenge}
 (D/(name+'.meta.json')).write_text(json.dumps(m,indent=2)+'\n');print(name,status,len(b),'challenge',challenge,err,flush=True)
