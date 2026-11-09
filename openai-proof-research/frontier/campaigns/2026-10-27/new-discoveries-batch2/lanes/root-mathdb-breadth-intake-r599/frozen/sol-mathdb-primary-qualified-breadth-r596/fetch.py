import urllib.request,json,pathlib,hashlib,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent;out=[]
for name,aid in [('dyck','0905.3764v1'),('derangement-primary','0803.2901v1'),('derangement-successor','1207.3878v1'),('furstenberg','0910.1956v1')]:
 url='https://arxiv.org/pdf/'+aid; row={'name':name,'url':url,'version':aid,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();row['response_url']=r.url
  assert b.startswith(b'%PDF');p=L/(name+'.pdf');p.write_bytes(b);row.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b),path=str(p));out.append(row)
  (L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(L/(name+'.txt'))],check=True,timeout=20)
  t=L/(name+'.txt');bb=t.read_bytes();row['derivative']={'path':str(t),'sha256':hashlib.sha256(bb).hexdigest(),'size':len(bb)}
 except Exception as e:row['failure']=str(e);out.append(row) if row not in out else None
 (L/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
