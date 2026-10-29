import urllib.request,hashlib,json,datetime,pathlib
D=pathlib.Path(__file__).resolve().parent
urls=[('shankar.html','https://arxiv.org/html/2609.15651v1'),('shankar-original.html','https://arxiv.org/html/2508.12467v1'),('liang.html','https://arxiv.org/html/2408.02782v2'),('omega-shankar.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/Library/Words/shankar2026canon.md'),('omega-shankar-proof.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/70af54071bfd4ac098619a9db8c16bb6f7aced11/D5/S0/Certificates/ShankarQStieltjesRefutation.lean')]
records=[]
for name,url in urls:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'source-evidence/'+name}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:
   r['status']=f.status; h=hashlib.sha256(); n=0
   with open(D/r['file'],'wb') as out:
    while b:=f.read(65536):
     n+=len(b)
     if n>3000000:raise ValueError('3MB response cap')
     h.update(b);out.write(b)
   r.update(bytes=n,sha256=h.hexdigest())
  head=(D/r['file']).read_text(errors='replace')[:1500].lower()
  if any(s in head for s in ['just a moment','verify you are human','captcha']):
   r['challenge']=True;records.append(r);break
 except Exception as e:r['error']=str(e)
 records.append(r)
(D/'http.json').write_text(json.dumps(records,indent=2))
print(json.dumps(records,indent=2))
