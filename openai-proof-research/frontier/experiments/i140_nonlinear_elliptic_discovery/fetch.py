from pathlib import Path
import urllib.request,hashlib,json,subprocess,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i140_nonlinear_elliptic_discovery';D=S/'external';D.mkdir(exist_ok=True)
items=[('bungert-page.html','https://arxiv.org/abs/2302.08462'),('bungert.pdf','https://arxiv.org/pdf/2302.08462'),('pqs.pdf','https://www-users.cse.umn.edu/~polacik/Publications/pqs1.pdf'),('qs-page.html','https://arxiv.org/abs/2407.04154'),('qs.pdf','https://arxiv.org/pdf/2407.04154'),('tw.pdf','https://maths-people.anu.edu.au/~wang/publications/affine.pdf')]
rows=[]
for name,url in items:
 row={'url':url,'requested_name':name,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=35) as f: b=f.read();row.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'))
  (D/name).write_bytes(b);row.update(path=str((D/name).relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF'):
   p=D/name;t=p.with_suffix('.txt');r=subprocess.run(['pdftotext','-layout',str(p),str(t)],capture_output=True,text=True);row.update(extraction_command=['pdftotext','-layout',row['path'],str(t.relative_to(R))],extraction_exit=r.returncode,extraction_stderr=r.stderr,text_path=str(t.relative_to(R)))
   if r.returncode==0:row.update(text_sha256=hashlib.sha256(t.read_bytes()).hexdigest(),splitlines=len(t.read_text().splitlines()))
 except Exception as e:row['error']=repr(e)
 rows.append(row);print(name,row.get('status'),row.get('bytes'),row.get('error',''),flush=True)
(S/'retrievals.json').write_text(json.dumps(rows,indent=2)+'\n')
