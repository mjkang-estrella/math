import pathlib,urllib.request,hashlib,json,datetime,subprocess
D=pathlib.Path(__file__).resolve().parents[1];receipts=[]
for i,num in [('365964','2411.17885'),('339996','1808.01074')]:
 url=f'https://arxiv.org/pdf/{num}v1'
 try:
  with urllib.request.urlopen(url,timeout=12) as f:b=f.read();status=f.status
  name=f'{i}-v1.pdf';(D/'sources'/name).write_bytes(b);subprocess.run(['pdftotext','-layout',str(D/'sources'/name),str(D/f'sources/{i}-v1.txt')],timeout=5)
  receipts.append(dict(url=url,status=status,file=name,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 except Exception as e:receipts.append(dict(url=url,error=str(e)))
(D/'sources/version-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(receipts)
