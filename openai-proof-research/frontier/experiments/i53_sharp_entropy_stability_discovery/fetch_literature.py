from pathlib import Path
import urllib.request, urllib.error, json, hashlib, datetime, subprocess
S=Path('frontier/sources/i53_sharp_entropy_stability_discovery/literature');S.mkdir(parents=True,exist_ok=True)
items=[('fms-abs','https://arxiv.org/abs/2406.07406'),('fms-v1','https://arxiv.org/pdf/2406.07406v1'),('fms-author','https://perso.math.u-pem.fr/fradelizi.matthieu/pdf/entropy-slicing-mahler-2024-06-14.pdf'),('mnr-abs','https://arxiv.org/abs/2309.01840'),('mnr-v2','https://arxiv.org/pdf/2309.01840v2'),('mnr-journal','https://link.springer.com/article/10.1007/s00440-025-01431-3'),('fk-abs','https://arxiv.org/abs/1008.4002'),('fk-v2','https://arxiv.org/pdf/1008.4002v2'),('odeco-v1','https://arxiv.org/pdf/1512.08031v1'),('kipp-journal','https://link.springer.com/article/10.1007/s00454-026-00829-7'),('rademacher-abs','https://arxiv.org/abs/1404.5662'),('rademacher-pdf','https://arxiv.org/pdf/1404.5662'),('auddy-yuan-abs','https://arxiv.org/abs/2007.09024'),('auddy-yuan-pdf','https://arxiv.org/pdf/2007.09024'),('mathdb','https://mathdb.com/database?search=isotropic')]
if (S/'manifest.json').exists():
 raise SystemExit('Captured literature manifest already exists; refusing to overwrite evidence.')
manifest=[]
for name,url in items:
 rec={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=35) as r: data=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
 except urllib.error.HTTPError as e:data=e.read();rec.update(status=e.code,error=str(e))
 except Exception as e:rec.update(error=repr(e));manifest.append(rec);continue
 ext='.pdf' if data.startswith(b'%PDF') else '.html';p=S/(name+ext);p.write_bytes(data);rec.update(path=str(p),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 if ext=='.pdf':
  t=p.with_suffix('.txt');q=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True);rec['text_extraction']={'returncode':q.returncode,'stderr':q.stderr,'path':str(t),'sha256':hashlib.sha256(t.read_bytes()).hexdigest() if t.exists() else None}
 manifest.append(rec);print(name,rec.get('status'),len(data),flush=True)
(S/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
