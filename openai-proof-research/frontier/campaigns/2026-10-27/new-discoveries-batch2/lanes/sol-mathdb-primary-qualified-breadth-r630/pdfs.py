from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
D=Path(__file__).resolve().parent
out=[]
for name,url in [('kapovich','https://www.math.ucdavis.edu/~kapovich/EPR/problems.pdf'),('baker-riley','https://pi.math.cornell.edu/~riley/papers/Cannon-Thurston_maps_do_not_always_exist/CT_counter.pdf'),('yaoyao','https://cs.purdue.edu/homes/weizhan/files/papers/yaoyao.pdf')]:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Mozilla/5.0','Accept':'application/pdf'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=r['headers']),timeout=25) as f:b=f.read(6000000);r.update(status=f.status,final_url=f.url)
  assert b.startswith(b'%PDF');p=D/(name+'.pdf');p.write_bytes(b);r.update(path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  # Persist byte binding before extraction.
  out.append(r);(D/'pdf-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  b=p.with_suffix('.txt').read_bytes();r['derivative']={'path':p.with_suffix('.txt').name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 except Exception as e:r['error']=str(e)
 if r not in out:out.append(r)
 (D/'pdf-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
