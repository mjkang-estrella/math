import pathlib,urllib.request,hashlib,json,subprocess,datetime
L=pathlib.Path(__file__).resolve().parent; out=[]
for a in ['1502.07934v2','1507.04290v4']:
 u='https://arxiv.org/pdf/'+a;r={'url':u,'version':a,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:d=f.read(10000000);r['status']=f.status
  p=L/'sources'/(a+'.pdf');p.write_bytes(d);r.update(path=str(p),sha256=hashlib.sha256(d).hexdigest());assert d.startswith(b'%PDF')
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=15);r['text_sha256']=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest()
 except Exception as e:r['failure']=str(e)
 out.append(r)
(L/'successor-bodies.json').write_text(json.dumps(out,indent=2)+'\n')
