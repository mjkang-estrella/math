import urllib.request,json,hashlib,datetime,sys,pathlib
P=pathlib.Path(__file__).parent
log=json.loads((P/'http.json').read_text()) if (P/'http.json').exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-check'}),timeout=25) as r:
   b=r.read(24000000); row.update(status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(P/'sources'/name).write_bytes(b)
 except Exception as e:row['error']=str(e)
 log.append(row);print(row)
 (P/'http.json').write_text(json.dumps(log,indent=2))
