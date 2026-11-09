import pathlib,json,hashlib,urllib.request,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent
out=[]
for aid in ['math/0405279','math/0511635','math/0702316']:
 url='https://arxiv.org/pdf/'+aid+'v1';name=aid.replace('/','-')+'v1';e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'v1'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=35) as f:b=f.read()
  assert b.startswith(b'%PDF');p=P/(name+'.pdf');p.write_bytes(b);e.update(pdf_sha256=hashlib.sha256(b).hexdigest(),pdf_size=len(b),pdf_path=p.name)
  out.append(e);(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(P/(name+'.txt'))],check=True)
  t=(P/(name+'.txt')).read_bytes();e.update(text_sha256=hashlib.sha256(t).hexdigest(),text_size=len(t),text_path=name+'.txt')
 except Exception as ex:e['failure']=str(ex);out.append(e) if e not in out else None
 (P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(e)
