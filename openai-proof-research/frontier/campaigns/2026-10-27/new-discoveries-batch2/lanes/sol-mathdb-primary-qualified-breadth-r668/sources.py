import pathlib,json,hashlib,urllib.request,datetime,subprocess
O=pathlib.Path(__file__).parent
out=[]
for name,url,ids in [('matroid','https://web.math.princeton.edu/~huh/MatroidHodge.pdf',[400164]),('tree','https://www.lamsade.dauphine.fr/~aharutyunyan/BTfinal.pdf',[400175]),('schmidt','https://arxiv.org/pdf/1001.2694v1',[400535])]:
 r=dict(name=name,url=url,ids=ids,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'})
  with urllib.request.urlopen(req,timeout=25) as f:b=f.read(15000000);r['final_url']=f.url
  assert b.startswith(b'%PDF');p=O/(name+'.pdf');p.write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b),status='bytes_bound_before_extraction')
  (O/'source-provenance.json').write_text(json.dumps(out+[r],indent=2)+'\n')
  t=O/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True,timeout=25)
  tb=t.read_bytes();r['derivative']=dict(path=str(t.resolve()),sha256=hashlib.sha256(tb).hexdigest(),size=len(tb));r['status']='PDF_and_text_bound_unread'
 except Exception as e:r.update(status='STOPPED',error=str(e))
 out.append(r);(O/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
