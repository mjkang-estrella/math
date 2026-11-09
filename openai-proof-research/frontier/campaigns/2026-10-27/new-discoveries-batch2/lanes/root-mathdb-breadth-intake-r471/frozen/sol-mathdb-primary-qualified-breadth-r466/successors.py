import pathlib,urllib.request,json,hashlib,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent; rows=[]
for i in ['1402.6539','1408.4093','1605.09173']:
 u='https://arxiv.org/pdf/'+i; row={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:b=f.read(12000000)
  assert b.startswith(b'%PDF'); p=L/'sources'/(i+'.pdf');p.write_bytes(b);row.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  t=p.with_suffix('.txt').read_bytes(); row['text_sha256_before_read']=hashlib.sha256(t).hexdigest();print(i,t.decode()[:14000])
 except Exception as e:row['failure']=str(e);print(row);rows.append(row);break
 rows.append(row)
(L/'successor-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
