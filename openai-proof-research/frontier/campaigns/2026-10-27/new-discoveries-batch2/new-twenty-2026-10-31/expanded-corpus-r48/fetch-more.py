exec(open(__file__.replace('fetch-more.py','fetch.py')).read().split('urls=')[0])
urls={'tensor-published':'https://pure.port.ac.uk/ws/portalfiles/portal/79417900/norm_extreme_final.pdf','welch-duals':'https://orbit.dtu.dk/files/198418560/2018CDK.pdf','game-published':'https://dirros.openscience.si/Dokument.php?id=28908&lang=eng','frame-published':'https://www.tandfonline.com/doi/pdf/10.1080/01630563.2022.2128818'}
receipts=[]
for name,url in urls.items():
 try:
  r=requests.get(url,timeout=20);d=r.content;ext='.pdf' if d.startswith(b'%PDF') else '.response';f=p/'sources'/(name+ext);f.write_bytes(d);rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'status':r.status_code,'final_url':r.url,'file':str(f),'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d)}
  if ext=='.pdf': subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=15,check=True)
 except Exception as e:rec={'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 receipts.append(rec);(p/'more-source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(name,rec.get('status'),rec.get('bytes'),flush=True)
