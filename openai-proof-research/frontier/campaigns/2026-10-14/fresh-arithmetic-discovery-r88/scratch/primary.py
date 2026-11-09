from pathlib import Path
import urllib.request,hashlib,json,subprocess
r=Path(__file__).resolve().parents[1];records=[]
for name,u in [('LLLMPZS2607v1','https://arxiv.org/pdf/2607.28411v1'),('HotchkissPerry2405v2','https://arxiv.org/pdf/2405.03315v2'),('RSW2108v1','https://arxiv.org/pdf/2108.10910v1')]:
 p=r/'packet/private/primary'/(name+'.pdf')
 try:
  resp=urllib.request.urlopen(u,timeout=45);data=resp.read();assert data.startswith(b'%PDF');p.write_bytes(data);out=p.with_suffix('.txt');pr=subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True,text=True);records.append({'name':name,'url':u,'final_url':resp.url,'sha256':hashlib.sha256(data).hexdigest(),'size':len(data),'text_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'extraction_stderr':pr.stderr,'returncode':pr.returncode});print(name,len(data),pr.stderr,flush=True)
 except Exception as e:records.append({'name':name,'url':u,'error':repr(e)});print(name,repr(e),flush=True)
(r/'packet/private/primary/register.json').write_text(json.dumps(records,indent=2)+'\n')
