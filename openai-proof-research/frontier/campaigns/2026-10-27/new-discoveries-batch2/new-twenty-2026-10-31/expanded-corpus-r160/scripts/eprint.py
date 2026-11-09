import pathlib,json,urllib.request,hashlib,datetime,sys,time
L=pathlib.Path(__file__).resolve().parents[1]
rp=L/'outputs/fetch-receipts.json'
receipts=json.loads(rp.read_text()) if rp.exists() else []
for t in sys.argv[1:]:
  k,a=t.split('|')
  url=f'https://arxiv.org/e-print/{a}'
  p=L/'sources/eprint'/f'{k}.eprint'
  try:
    with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence collection (python urllib)'}),timeout=30) as s:
      data=s.read(); status=s.status; ct=s.headers.get('Content-Type')
    p.write_bytes(data)
    r=dict(id=k,url=url,status=status,content_type=ct,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),file=str(p.relative_to(L)))
  except Exception as e:
    r=dict(id=k,url=url,error=repr(e)[:300])
  r['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
  receipts.append(r); rp.write_text(json.dumps(receipts,indent=1)); print(json.dumps(r),flush=True)
  if 'error' in r and ('403' in r['error'] or '429' in r['error']): print('STOP'); break
  time.sleep(2)
