import requests,pathlib,json,hashlib,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
p=pathlib.Path(__file__).resolve().parent
urls={'cnat-selig':'https://arxiv.org/pdf/2303.15756','myers':'https://arxiv.org/pdf/2210.03262','additive':'https://arxiv.org/pdf/2211.01893','kemeny-bini':'https://arxiv.org/pdf/2504.01127','queens-published':'https://link.springer.com/article/10.1007/s40687-024-00492-5','kemeny-abstract':'https://arxiv.org/abs/2211.01495','paths-new':'https://dmtcs.episciences.org/15665/pdf'}
rout=[]
for name,url in urls.items():
 try:
  r=requests.get(url,timeout=15);raw=r.content;ext='pdf' if raw.startswith(b'%PDF') else 'html';f=p/'sources'/f'{name}.{ext}';f.write_bytes(raw);entry={'name':name,'url':url,'final_url':r.url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'file':str(f.relative_to(p)),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=10)
 except Exception as e:entry={'name':name,'url':url,'error':str(e)}
 rout.append(entry);(p/'extra-source-receipts.json').write_text(json.dumps(rout,indent=2));print(entry,flush=True)
