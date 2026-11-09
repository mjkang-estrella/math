import pathlib,urllib.request,urllib.error,datetime,hashlib,json,subprocess
L=pathlib.Path(__file__).resolve().parent;out=[]
for a in ['2311.12302','2309.04460','2206.02689']:
 u='https://arxiv.org/pdf/'+a;e={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read(10000000);e['status']=r.status
  p=L/'sources'/('arxiv-'+a+'.pdf');p.write_bytes(b);e.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));e['extraction_exit']=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))]).returncode
 except Exception as ex:
  e.update(status='HOLD',error=str(ex));out.append(e)
  if isinstance(ex,urllib.error.HTTPError) and ex.code in [403,429]:break
  continue
 out.append(e)
(L/'successor-bodies-access.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
