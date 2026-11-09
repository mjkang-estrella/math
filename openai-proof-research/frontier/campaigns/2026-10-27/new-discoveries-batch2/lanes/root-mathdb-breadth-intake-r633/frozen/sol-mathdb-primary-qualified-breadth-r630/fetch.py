from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).resolve().parent
urls=[('topp60','https://topp.openproblem.net/p60'),('topp70','https://topp.openproblem.net/p70'),('topp43','https://topp.openproblem.net/p43'),('cooper','https://people.math.sc.edu/cooper/combprob.html'),('eremenko','https://www.math.purdue.edu/~eremenko/uns1.html')]
out=[]
for name,url in urls:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Mozilla/5.0','Accept':'text/html,application/pdf;q=0.9,*/*;q=0.8'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=r['headers']),timeout=25) as f:
   b=f.read(6000000);r.update(status=f.status,final_url=f.url)
  p=D/(name+'.html');p.write_bytes(b);r.update(path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:r['error']=str(e)
 out.append(r)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
