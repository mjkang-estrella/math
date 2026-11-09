import pathlib,json,urllib.request,hashlib,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((D/'extracted.json').read_text()); receipts=[]
for i,o in r.items():
 url=o['source_url'].replace('/abs/','/pdf/')
 try:
  with urllib.request.urlopen(url,timeout=12) as f: b=f.read();status=f.status;final=f.url
  (D/f'sources/{i}.pdf').write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(D/f'sources/{i}.pdf'),str(D/f'sources/{i}.txt')],timeout=8)
  receipt=dict(id=i,url=url,final_url=final,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:receipt=dict(id=i,url=url,error=str(e))
 receipt['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipts.append(receipt)
 (D/'sources/receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
 print(receipt,flush=True)
