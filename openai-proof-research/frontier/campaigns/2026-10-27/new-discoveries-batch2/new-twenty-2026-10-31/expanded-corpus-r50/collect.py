import pathlib,requests,hashlib,json,datetime,subprocess,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
p=pathlib.Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
urls={'registry-math':'https://api.github.com/repos/openai/math/commits/main','registry-omega':'https://api.github.com/repos/teorth/omega/commits/main','queens':'https://arxiv.org/pdf/2211.05651','subrings':'https://arxiv.org/pdf/2211.16595','kemeny':'https://arxiv.org/pdf/2211.01495','cnat':'https://dmtcs.episciences.org/13114/pdf','connected':'https://arxiv.org/pdf/2210.11032','codes':'https://arxiv.org/pdf/2210.06241','choosability':'https://arxiv.org/pdf/2211.00622','weak-nkt':'https://arxiv.org/pdf/2210.08370','cycle-classes':'https://arxiv.org/pdf/2210.15354','odd-induced':'https://arxiv.org/pdf/2211.10895','odd-holes':'https://arxiv.org/pdf/2301.00112'}
receipts=[]
for name,url in urls.items():
 try:
  r=requests.get(url,timeout=18);raw=r.content;ext='pdf' if raw.startswith(b'%PDF') else 'json' if name.startswith('registry') else 'html';f=p/'sources'/f'{name}.{ext}';f.write_bytes(raw);entry={'name':name,'url':url,'final_url':r.url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'file':str(f.relative_to(p)),'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
  if ext=='pdf':subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=15)
 except Exception as e:entry={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'error':str(e)}
 receipts.append(entry);(p/'source-receipts.json').write_text(json.dumps(receipts,indent=2));print(entry,flush=True)
