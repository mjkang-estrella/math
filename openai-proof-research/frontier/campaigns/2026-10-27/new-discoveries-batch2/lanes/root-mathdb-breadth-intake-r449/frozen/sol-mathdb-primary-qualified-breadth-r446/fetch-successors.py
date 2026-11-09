import urllib.request,urllib.error,pathlib,hashlib,json,subprocess,datetime
R=pathlib.Path(__file__).resolve().parent;out=[]
for n,a in [('sumcomplex','0903.1359'),('treecover','1902.05055'),('treecover-successor','2109.02569'),('boolean','1711.08215')]:
 u='https://arxiv.org/pdf/'+a
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read(12000000)
  p=R/'sources'/f'{n}.pdf';p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  out.append({'url':u,'file':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'status':'downloaded','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 except Exception as e:
  out.append({'url':u,'status':'HOLD','error':str(e)})
  if isinstance(e,urllib.error.HTTPError) and e.code in (403,429):break
(R/'successor-access.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
