import pathlib,json,urllib.request,datetime,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
for i,o in json.loads((D/'extracted.json').read_text()).items():
 url=o['source_url'];r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=5) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  (D/f'sources/{i}.abs.html').write_bytes(b)
 except Exception as e:r['error']=str(e)
 (D/f'sources/{i}.abs.receipt.json').write_text(json.dumps(r,indent=2))
 print(i,r,flush=True)
