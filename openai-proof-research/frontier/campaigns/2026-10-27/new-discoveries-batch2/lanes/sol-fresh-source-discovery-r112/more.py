exec(compile(open(__file__.replace('more.py','fetch.py')).read().split('urls=')[0], 'fetch-prefix', 'exec'))
urls={'fu-v5':'https://arxiv.org/html/2409.12404v5','lages':'https://arxiv.org/html/2405.11660v1','ahk':'https://annals.math.princeton.edu/wp-content/uploads/annals-v188-n2-p01-p.pdf','zaslav':'https://people.math.binghamton.edu/zaslav/Papers/bg2.pdf'}
with (L/'more-http.jsonl').open('w') as log:
 for name,url in urls.items():
  row={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  try:
   h=hashlib.sha256();n=0
   ext='pdf' if url.endswith('.pdf') else 'html'
   with urllib.request.urlopen(url,timeout=25) as r,(L/'inputs'/f'{name}.{ext}').open('wb') as f:
    row['status']=r.status
    while b:=r.read(32768):f.write(b);h.update(b);n+=len(b)
   row.update(bytes=n,sha256=h.hexdigest())
   if ext=='html':
    p=Parser()
    with (L/'inputs'/f'{name}.txt').open('w') as out,(L/'inputs'/f'{name}.html').open() as f:
     p.out=out
     while b:=f.read(32768):p.feed(b)
  except Exception as e:row['error']=str(e)
  log.write(json.dumps(row)+'\n');log.flush();print(json.dumps(row),flush=True)
