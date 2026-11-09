import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'extracted.json').read_text())
for i in sys.argv[1:]:
 a=rows[i]['source_url'].split('/')[-1]
 for kind,url in [('abs','https://arxiv.org/abs/'+a),('pdf','https://arxiv.org/pdf/'+a)]:
  receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematics research source verification'}),timeout=12) as r:
    data=r.read();receipt.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
   (D/f'sources/{i}.{kind}').write_bytes(data)
  except Exception as e: receipt.update(error=str(e))
  (D/f'sources/{i}.{kind}.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
  print(i,kind,receipt,flush=True)
