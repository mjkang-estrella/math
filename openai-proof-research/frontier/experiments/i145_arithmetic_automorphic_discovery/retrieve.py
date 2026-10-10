from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
s=Path(__file__).resolve().parents[3]/'frontier/sources/i145_arithmetic_automorphic_discovery/primary'; rec=[]
urls={'aka-abs':'https://arxiv.org/abs/1403.2016','aka':'https://people.math.ethz.ch/~einsiedl/partDuke4.pdf','elmv09-abs':'https://arxiv.org/abs/math/0607815','elmv09':'https://arxiv.org/pdf/math/0607815','elmv11-abs':'https://arxiv.org/abs/0708.1113','elmv11':'https://www.ma.huji.ac.il/~elon/Publications/ELMV3.pdf','khayutin-abs':'https://arxiv.org/abs/1510.08481','lotz-search':'https://arxiv.org/search/?query=Lemke+Oliver+Thorner+Zaman&searchtype=author','newton-abs':'https://arxiv.org/abs/1912.11265','ciubotaru':'https://arxiv.org/abs/2311.01104','roe-abs':'https://arxiv.org/abs/0804.1662','ito-abs':'https://arxiv.org/abs/1202.6662','dumnicki-abs':'https://arxiv.org/abs/math/0606716','biran-abs':'https://arxiv.org/abs/alg-geom/9705018'}
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
