import pathlib,urllib.request,datetime,json,hashlib,subprocess
L=pathlib.Path(__file__).resolve().parent;log=json.loads((L/'http.json').read_text());h=json.loads((L/'heads.json').read_text())['omega']
urls={'psZ.pdf':'https://discovery.ucl.ac.uk/id/eprint/10101894/1/1807.03271v2.pdf','zhu.html':'https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/jlms.70450','omega-corrected-delta.json':f'https://api.github.com/repos/the-omega-institute/trureturing/compare/6f8ee6614e0faf9dfa2cce46d1eb758dea97c335...{h}','cigler.md':f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/Problems/cigler-narayana-strip-product.md'}
for n,u in urls.items():
 r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as f:b=f.read(18000000);r.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (L/'sources'/n).write_bytes(b)
  if n.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 log.append(r)
(L/'http.json').write_text(json.dumps(log,indent=2));print(json.dumps(log[-4:],indent=2))
