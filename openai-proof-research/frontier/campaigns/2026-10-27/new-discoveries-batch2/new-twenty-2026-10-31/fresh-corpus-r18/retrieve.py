import pathlib, urllib.request, hashlib, json, datetime, subprocess
P=pathlib.Path(__file__).parent
S=P/'sources'; S.mkdir(exist_ok=True)
urls={'circular-prior':'https://hexagonmath.org/pdf/2610.00473v2',
      'convex-prior':'https://malayajournal.org/articles/MJM0S201153.pdf'}
receipts=json.loads((P/'source-receipts.json').read_text())
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'}),timeout=25) as q:
   b=q.read(); r.update(status=q.status,final_url=q.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  f=S/(name+('.json' if name=='registry-head' else '.pdf'));f.write_bytes(b)
  if name!='registry-head':
   c=subprocess.run(['pdftotext','-layout',str(f),str(S/(name+'.txt'))],capture_output=True,text=True,timeout=15)
   r['pdftotext']={'exit':c.returncode,'stderr':c.stderr}
 except Exception as e:r['error']=str(e)
 receipts.append(r)
 (P/'source-receipts.json').write_text(json.dumps(receipts,indent=2))
 print(json.dumps(r),flush=True)
