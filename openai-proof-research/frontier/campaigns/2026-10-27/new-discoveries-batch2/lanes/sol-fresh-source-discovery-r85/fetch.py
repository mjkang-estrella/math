import urllib.request,hashlib,json,datetime,sys,pathlib
base=pathlib.Path(__file__).parent
records=[]
for name,url in [a.split('=',1) for a in sys.argv[1:]]:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:
   b=f.read(16000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(base/'sources'/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 records.append(r)
p=base/'http.json';old=json.loads(p.read_text()) if p.exists() else [];p.write_text(json.dumps(old+records,indent=2));print(json.dumps(records,indent=2))
