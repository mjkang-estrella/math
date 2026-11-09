exec(open(__file__.replace('fetch_more.py','fetch.py')).read().split('urls=')[0])
urls={'italian-2021':'https://arxiv.org/pdf/2011.01078','kk-published':'https://repository.nie.edu.sg/server/api/core/bitstreams/2b6baca2-04f5-414b-92b8-15dabc772a99/content','omega-readme':'https://raw.githubusercontent.com/the-omega-institute/trureturing/95454f1bac7a754ed76e5e32426fb3beb13a6669/README.md','omega-tree':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/95454f1bac7a754ed76e5e32426fb3beb13a6669?recursive=1'}
for name,url in urls.items():
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  r=requests.get(url,timeout=25);rec.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content));p=w/'sources'/name;p.write_bytes(r.content)
  if r.status_code==200 and r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True,timeout=20)
 except Exception as e:rec['error']=str(e)
 receipts.append(rec);print(json.dumps(rec),flush=True);(w/'sources/more-receipts.json').write_text(json.dumps(receipts,indent=2))
