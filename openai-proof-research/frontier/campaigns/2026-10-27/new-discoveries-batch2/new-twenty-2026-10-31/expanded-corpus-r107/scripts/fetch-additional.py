import pathlib,json,urllib.request,urllib.error,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
urls={'https://arxiv.org/pdf/1903.08266','https://arxiv.org/pdf/2211.09772','https://link.springer.com/content/pdf/10.1007/s10623-022-01145-w.pdf','https://ajc.maths.uq.edu.au/pdf/89/ajc_v89_p305.pdf','https://nisc.com/products/abstracts/38287/proofs-of-three-conjectured-internal-congruences-modulo-32-for-schur-type-overpartitions'}

receipts=[]
for url in sorted(urls):
 name=url.rsplit('/',1)[-1]
 p=D/'sources'/name
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Math research source review'}),timeout=15) as f:
   data=f.read();rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.write_bytes(data)
  if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True)
 except Exception as e:rec.update(error=str(e))
 receipts.append(rec);(D/'sources/additional-fetch-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(rec,flush=True)
