import pathlib,urllib.request,json,hashlib,datetime
L=pathlib.Path(__file__).parent
urls={'omega-current.md':'https://raw.githubusercontent.com/the-omega-institute/trureturing/2b143c68ca72fcaccfe71d6233cb2c6db4c8c059/Problems/zhang-2026-threshold-hypergraph-independence-polynomial.md','journal-current.html':'https://amc-journal.eu/index.php/amc/article/view/3383','journal-current.pdf':'https://amc-journal.eu/index.php/amc/article/download/3383/2273','survey-index.html':'https://mc.sbm.org.br/volumes/volume-45/'}
rows=[]
for name,url in urls.items():
 r={'url':url,'name':name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:
   b=f.read(3000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(L/name).write_bytes(b)
  if name.endswith('.md'):print(b.decode())
 except Exception as e:r['error']=str(e)
 rows.append(r);print(json.dumps(r))
(L/'http.json').write_text(json.dumps(rows,indent=2)+'\n')
