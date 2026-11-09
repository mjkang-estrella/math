import urllib.request,pathlib,json,datetime,hashlib,subprocess
L=pathlib.Path(__file__).parent/'prior'
for ident,name in [('1607.05675v2','set-reconstruction'),('1701.07667v1','sceneries')]:
 url='https://arxiv.org/pdf/'+ident;r={'url':url,'utc':str(datetime.datetime.now(datetime.timezone.utc))}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers));data=f.read(5000001);assert len(data)<=5000000 and data.startswith(b'%PDF')
  p=L/(name+'.pdf');p.write_bytes(data);h=hashlib.sha256(data).hexdigest();r.update(sha256=h,bytes=len(data))
  # Bind complete primary bytes before extraction; bind text before any reading.
  (L/(name+'.receipt.json')).write_text(json.dumps(r,indent=2))
  out=L/(name+'.txt');res=subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True,text=True,timeout=40)
  assert res.returncode==0 and hashlib.sha256(p.read_bytes()).hexdigest()==h
  ex={'pdf_sha256':h,'text_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'returncode':res.returncode,'stderr':res.stderr}
  (L/(name+'.extract.json')).write_text(json.dumps(ex,indent=2));print(name,r['sha256'],ex)
 except Exception as e:r['error']=repr(e);print(r)
 (L/(name+'.receipt.json')).write_text(json.dumps(r,indent=2))
