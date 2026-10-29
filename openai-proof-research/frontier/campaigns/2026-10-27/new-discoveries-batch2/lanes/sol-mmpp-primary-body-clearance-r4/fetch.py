import urllib.request,urllib.error,pathlib,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parent;S=L/'sources';S.mkdir(exist_ok=True); log=L/'access.json';rows=json.loads(log.read_text()) if log.exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':name,'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research primary-source comparison (public access only)'}),timeout=22) as f:
   b=f.read(20000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(S/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 rows.append(r);log.write_text(json.dumps(rows,indent=2));print(json.dumps(r),flush=True)
