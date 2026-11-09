import pathlib; exec((pathlib.Path(__file__).parent/'fetch.py').read_text().split('urls=')[0])
receipts=json.loads((p/'source-receipts.json').read_text())
urls={'benes-primary.pdf':'https://cs-people.bu.edu/tromer/papers/ramreduce-20120818.pdf','edgecolor-2023.pdf':'https://www.math.md/files/basm/y2023-n3/y2023-n3-%28pp26-36%29.pdf.pdf'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as q:data=q.read();r.update(status=q.status,final_url=q.url)
  (p/'sources'/name).write_bytes(data);r.update(path=name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],timeout=15,check=True)
 except Exception as e:r['error']=str(e)
 receipts.append(r);(p/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(r,flush=True)
