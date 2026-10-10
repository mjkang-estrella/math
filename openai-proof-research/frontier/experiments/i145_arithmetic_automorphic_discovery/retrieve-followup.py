from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
s=Path(__file__).resolve().parents[3]/'frontier/sources/i145_arithmetic_automorphic_discovery/primary'; rec=[]
urls={'aka-current':'https://arxiv.org/pdf/1403.2016v2','elmv11-current':'https://arxiv.org/pdf/0708.1113v2','lotz-abs':'https://arxiv.org/abs/2012.14422','lotz-current':'https://arxiv.org/pdf/2012.14422','khayutin-current':'https://arxiv.org/pdf/1510.08481v2'}
rec=json.loads((s/'retrievals.json').read_text())
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as h:b=h.read();r.update(status=h.status,final_url=h.url,headers=dict(h.headers))
  ext='pdf' if b.startswith(b'%PDF') else 'html';p=s/(name+'.'+ext);p.write_bytes(b);r.update(file=str(p.relative_to(s)),sha256=hashlib.sha256(b).hexdigest())
  if ext=='pdf':
   t=s/(name+'.txt');z=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True);r.update(extraction_exit=z.returncode,extraction_stderr=z.stderr)
   if t.exists():r.update(text=t.name,text_sha256=hashlib.sha256(t.read_bytes()).hexdigest())
 except Exception as e:r['failure']=repr(e)
 rec.append(r);(s/'retrievals.json').write_text(json.dumps(rec,indent=2)+'\n');print(name,r.get('status',r.get('failure')),flush=True)
