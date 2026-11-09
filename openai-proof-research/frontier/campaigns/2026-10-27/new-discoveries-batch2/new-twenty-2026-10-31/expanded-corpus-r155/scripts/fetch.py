import pathlib,urllib.request,urllib.error,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((L/'outputs/intake.json').read_text())
for i in sys.argv[1:]:
 a=rows[i]['record']['source_url'].split('/')[-1]
 for kind,url in [('abs',f'https://arxiv.org/abs/{a}'),('pdf',f'https://arxiv.org/pdf/{a}')]:
  receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   with urllib.request.urlopen(url,timeout=9) as r:
    b=r.read(); receipt.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=r.url)
    (L/f'sources/{i}.{kind}').write_bytes(b)
  except Exception as e: receipt['error']=str(e)
  with (L/'outputs/http.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
  print(i,kind,receipt,flush=True)
