from pathlib import Path
import urllib.request,datetime,json,hashlib,subprocess
D=Path(__file__).resolve().parent
out=json.loads((D/'source-provenance.json').read_text())
for name,url in [('wecken-successor','https://arxiv.org/pdf/1204.4808v1')]:
 t=datetime.datetime.now(datetime.timezone.utc).isoformat();e={'name':name,'url':url,'utc':t}
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read();e['final_url']=r.url
  e.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());(D/(name+'.pdf')).write_bytes(b)
  out.append(e);(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(D/(name+'.pdf')),str(D/(name+'.txt'))],check=True)
  b=(D/(name+'.txt')).read_bytes();e['derivative']={'path':name+'.txt','size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as ex:e['failure']=repr(ex);out.append(e) if e not in out else None
 (D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
 print(e)
