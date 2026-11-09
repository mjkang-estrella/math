import pathlib,json,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
receipts=[]
for r in json.loads((L/'reservation.json').read_text())['rows']:
 k=r['mathdb_id']; a=r['source_url'].split('/')[-1]
 for typ in ['abs','html']:
  url=f'https://arxiv.org/{typ}/{a}'
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence collection'}),timeout=18) as s:
    data=s.read(); status=s.status
   p=L/'sources'/f'{k}.{typ}';p.write_bytes(data)
   receipt=dict(id=k,url=url,status=status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),file=str(p))
  except Exception as e:receipt=dict(id=k,url=url,error=str(e))
  receipt['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
  receipts.append(receipt)
  (L/'outputs/fetch-receipts.json').write_text(json.dumps(receipts,indent=2))
  print(receipt,flush=True)
