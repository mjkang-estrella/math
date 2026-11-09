import pathlib,json,urllib.request,urllib.error,datetime,hashlib,sys
L=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((L/'reservation.json').read_text())['rows']
for row in rows[int(sys.argv[1]):int(sys.argv[2])]:
 aid=row['source_url'].split('/')[-1]
 for kind,url in [('abs',row['source_url']),('pdf','https://arxiv.org/pdf/'+aid)]:
  p=L/'sources'/f'{aid}.{kind}'; rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  if p.with_suffix(p.suffix+'.receipt.json').exists(): continue
  try:
   with urllib.request.urlopen(url,timeout=15) as r: data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
  except Exception as e: rec.update(error=str(e),status=getattr(e,'code',None))
  p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(rec,indent=2)); print(aid,kind,rec.get('status'),rec.get('bytes'),flush=True)
