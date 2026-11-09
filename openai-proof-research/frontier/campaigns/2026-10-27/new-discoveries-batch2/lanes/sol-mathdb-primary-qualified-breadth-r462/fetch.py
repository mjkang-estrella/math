import urllib.request,urllib.error,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
a=json.loads((L/'assigned-records.json').read_text()); ids={322219,322250,322282,323693,324496,324568,324569,323515,323760,323822,324362}
log=[]
for x in a:
 r=x['record']
 if r['mathdb_id'] not in ids:continue
 u=r['source_url'].replace('/abs/','/html/')
 try:
  res=urllib.request.urlopen(u,timeout=20);b=res.read();p=L/'sources'/f"{r['mathdb_id']}.html";p.write_bytes(b)
  log.append(dict(id=r['mathdb_id'],url=u,final_url=res.url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path=str(p),version='unversioned endpoint; body version requires inspection'))
 except Exception as e:
  log.append(dict(id=r['mathdb_id'],url=u,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),failure=str(e),policy='No retry or alternate route for this source'))
  print(r['mathdb_id'],str(e),flush=True)
 (L/'source-receipts.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps(log,indent=2))
