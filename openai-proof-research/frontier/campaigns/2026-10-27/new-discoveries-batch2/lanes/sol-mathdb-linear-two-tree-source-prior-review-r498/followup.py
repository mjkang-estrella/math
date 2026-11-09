import pathlib,urllib.request,hashlib,json,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent; rows=[]
for name,url in [('evans-cv.pdf','https://math.byu.edu/0000018b-abad-d20e-abab-abbdccd20000/evanscv-pdf'),('1901.00053v3.pdf','https://arxiv.org/pdf/1901.00053v3'),('1712.05859-abs.html','https://arxiv.org/abs/1712.05859v1')]:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  (L/name).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());(L/'followup-bindings.json').write_text(json.dumps(rows+[r],indent=2)+'\n')
  if b.startswith(b'%PDF'):
   p=L/name;t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True);b=t.read_bytes();r['derivative']={'path':str(t),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as e:r['failure']=str(e)
 rows.append(r);(L/'followup-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows))
