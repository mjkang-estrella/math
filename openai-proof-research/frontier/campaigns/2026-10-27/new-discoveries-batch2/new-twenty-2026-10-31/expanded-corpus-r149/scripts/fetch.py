import pathlib,json,urllib.request,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((L/'reservation.json').read_text())['rows']
receipts=[]
for r in rows[int(sys.argv[1]):int(sys.argv[2])]:
 a=r['source_url'].split('/')[-1]; i=r['mathdb_id']
 for kind in ['abs','pdf']:
  url=f'https://arxiv.org/{kind}/{a}'
  try:
   with urllib.request.urlopen(url,timeout=15) as f:
    b=f.read(); status=f.status; final=f.url
   (L/f'sources/{i}.{kind}').write_bytes(b)
   row=dict(id=i,url=url,final_url=final,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  except Exception as e:row=dict(id=i,url=url,error=str(e))
  row['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipts.append(row)
  print(json.dumps(row),flush=True)
(L/f'outputs/fetch-{sys.argv[1]}-{sys.argv[2]}.json').write_text(json.dumps(receipts,indent=2))
