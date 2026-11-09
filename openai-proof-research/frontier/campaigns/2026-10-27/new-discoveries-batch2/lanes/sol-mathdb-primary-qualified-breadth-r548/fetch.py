import pathlib,urllib.request,json,hashlib,datetime,subprocess
P=pathlib.Path(__file__).resolve().parent
urls={'gaussian.pdf':'https://swh.princeton.edu/~rvan/migrated-to-math-2018-06-20/dimfr171101.pdf','gehring.pdf':'https://www.jasoncantarella.com/downloads/papers/ropcrit/gehrcrit_final.pdf','gaussian-question.html':'https://afonsobandeira.wordpress.com/2015/10/25/10l42concentration/'}
out=[]
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as resp:b=resp.read();r.update(final_url=resp.url,status=resp.status)
  (P/name).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());out.append(r)
 except Exception as ex:r['failure']=str(ex);out.append(r)
 (P/'downloads.json').write_text(json.dumps(out,indent=2)+'\n')
 if 'failure' not in r and name.endswith('.pdf'):
  subprocess.run(['pdftotext','-layout',str(P/name),str(P/name.replace('.pdf','.txt'))],check=True)
  p=P/name.replace('.pdf','.txt');b=p.read_bytes();r['derivative']={'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
  (P/'downloads.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
