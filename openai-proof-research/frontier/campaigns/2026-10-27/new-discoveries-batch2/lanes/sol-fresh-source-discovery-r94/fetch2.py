exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=')[0])
urls={'bnt':'https://arxiv.org/pdf/1509.05926','lt':'https://arxiv.org/pdf/2001.06439','luo-abs':'https://arxiv.org/abs/2609.11418','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','openai-head':'https://api.github.com/repos/openai/math/commits/HEAD'}
rows=json.loads((p/'http.json').read_text())
for key,url in urls.items():
 r={'key':key,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(6000000);r['status']=f.status
  suf='.pdf' if b.startswith(b'%PDF') else '.json' if key.endswith('head') else '.html'
  dest=p/'sources'/(key+suf);dest.write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if suf=='.pdf':subprocess.run(['pdftotext','-layout',str(dest),str(dest.with_suffix('.txt'))],check=True)
 except Exception as e:r['error']=str(e)
 rows.append(r)
(p/'http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows[-5:],indent=2))
