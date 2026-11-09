import requests,pathlib,json,hashlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
p=pathlib.Path(__file__).resolve().parent
urls={'omega-albright-proof':'https://raw.githubusercontent.com/the-omega-institute/trureturing/d7af67136d4478875778ac6e75eb5fbb8b3693a5/D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.lean','omega-albright-problem':'https://raw.githubusercontent.com/the-omega-institute/trureturing/d7af67136d4478875778ac6e75eb5fbb8b3693a5/Problems/albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5.md'}
rout=[]
for name,url in urls.items():
 try:
  r=requests.get(url,timeout=15);raw=r.content;ext='pdf' if raw.startswith(b'%PDF') else 'html';f=p/'sources'/f'{name}.{ext}';f.write_bytes(raw);entry={'name':name,'url':url,'final_url':r.url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'file':str(f.relative_to(p)),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=10)
 except Exception as e:entry={'name':name,'url':url,'error':str(e)}
 rout.append(entry);(p/'prior-proof-receipts.json').write_text(json.dumps(rout,indent=2));print(entry,flush=True)
