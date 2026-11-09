exec(open(__file__.replace('fetch_more.py','fetch.py')).read().split('urls=')[0])
receipts=json.loads((p/'source-receipts.json').read_text())
urls={'superconcentrators.pdf':'https://www.internetmathematicsjournal.com/article/1379.pdf','posets.pdf':'https://arxiv.org/pdf/1806.04489','dg.pdf':'https://arxiv.org/pdf/1805.09283','wellcovered.pdf':'https://arxiv.org/pdf/1807.06914'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as q:data=q.read();r.update(status=q.status,final_url=q.url)
  (p/'sources'/name).write_bytes(data);r.update(path=name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],timeout=15,check=True)
 except Exception as e:r['error']=str(e)
 receipts.append(r);(p/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(r,flush=True)
