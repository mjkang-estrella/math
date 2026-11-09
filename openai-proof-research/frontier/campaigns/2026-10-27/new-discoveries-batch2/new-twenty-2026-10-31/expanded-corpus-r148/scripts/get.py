import pathlib,urllib.request,json,sys,datetime,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 p=L/'sources'/name
 if p.with_name(p.name+'.receipt.json').exists():continue
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:b=r.read();p.write_bytes(b);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:rec.update(status=getattr(e,'code',None),error=str(e))
 p.with_name(p.name+'.receipt.json').write_text(json.dumps(rec,indent=2));print(name,rec.get('status'),rec.get('bytes'),flush=True)
