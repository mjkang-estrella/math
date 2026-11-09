import pathlib,json,urllib.request,hashlib,datetime,sys,time
L=pathlib.Path(__file__).resolve().parents[1]
rp=L/'outputs/fetch-receipts.json'
receipts=json.loads(rp.read_text()) if rp.exists() else []
targets=sys.argv[1:]  # items like id:typ:url
for t in targets:
  k,typ,url=t.split('|',2)
  p=L/'sources'/f'{k}.{typ}'
  try:
    with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence collection (python urllib)'}),timeout=20) as s:
      data=s.read(); status=s.status
    p.write_bytes(data)
    r=dict(id=k,url=url,status=status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),file=str(p.relative_to(L)))
  except Exception as e:
    r=dict(id=k,url=url,error=repr(e)[:300])
  r['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
  receipts.append(r); rp.write_text(json.dumps(receipts,indent=1))
  print(json.dumps(r),flush=True)
  if 'error' in r and ('403' in r['error'] or '429' in r['error']): print('STOP on denial'); break
  time.sleep(1.5)
