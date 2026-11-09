import urllib.request,urllib.error,datetime,hashlib,json,pathlib,subprocess
W=pathlib.Path(__file__).resolve().parent;(W/'sources').mkdir(exist_ok=True)
jobs=[('registry','https://api.github.com/repos/openai/math/commits/main'),('tapp','https://arxiv.org/pdf/2401.17947v3'),('models','https://jamie.tuckerfoltz.com/Papers/2026-04-Treehouse/main.pdf'),('livingston','https://msp.org/agt/2010/10-4/agt-v10-n4-p10-p.pdf')]
for name,url in jobs:
 receipt=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=25) as f:
   data=f.read(15000000);receipt.update(status=f.status,final_url=f.url,headers=dict(f.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  p=W/'sources'/(name+('.json' if name=='registry' else '.pdf'));p.write_bytes(data)
  if name!='registry':
   result=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,timeout=20);receipt['extraction_returncode']=result.returncode;receipt['extraction_stderr']=result.stderr.decode()
 except Exception as e:receipt.update(error=str(e),status=getattr(e,'code',None))
 (W/'sources'/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(name,receipt.get('status'),receipt.get('sha256'),receipt.get('error',''),flush=True)
