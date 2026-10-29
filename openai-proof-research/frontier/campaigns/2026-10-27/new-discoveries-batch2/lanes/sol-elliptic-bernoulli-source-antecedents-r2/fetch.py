import requests,pathlib,json,datetime,hashlib,resource,sys
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(40,)*2)
o=pathlib.Path(__file__).parent; log=json.loads((o/'http.json').read_text()) if (o/'http.json').exists() else []
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(url,timeout=(10,25),stream=True); data=bytearray()
  for chunk in r.iter_content(65536):
   data.extend(chunk)
   if len(data)>12*1024**2: raise RuntimeError('12MiB cap exceeded; not a complete source')
  p=o/'sources'/name;p.write_bytes(data);row.update(status=r.status_code,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),content_type=r.headers.get('Content-Type'),file=str(p))
 except Exception as e:row['error']=str(e)
 log.append(row);(o/'http.json').write_text(json.dumps(log,indent=2));print(row)
