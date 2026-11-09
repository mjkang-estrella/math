import pathlib,json,urllib.request,urllib.error,hashlib,datetime,time,subprocess
L=pathlib.Path(__file__).resolve().parents[1];(L/'sources').mkdir(exist_ok=True);rs=json.loads((L/'statements.json').read_text());urls={x['record']['source_url'] for x in rs};out=[];start=time.monotonic();stopped=False
for url in sorted(urls):
 target=url.replace('/abs/','/pdf/');ident=target.rsplit('/',1)[1];row=dict(url=target,record_source_url=url,requested_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version='unversioned arXiv latest endpoint; exact retained bytes fixed by hash',ids=[x['record']['mathdb_id'] for x in rs if x['record']['source_url']==url])
 if stopped or time.monotonic()-start>195:row['status']='not_attempted_host_stop_or_wall_budget';out.append(row);continue
 try:
  with urllib.request.urlopen(urllib.request.Request(target,headers={'User-Agent':'Research-source-review/1.0'}),timeout=10) as r:
   b=r.read(12*1024*1024);row.update(http_status=r.status,final_url=r.url)
  if not b.startswith(b'%PDF'):raise ValueError('not PDF; no alternate route attempted')
  p=L/'sources'/f'{ident}.pdf';p.write_bytes(b);row.update(status='retained',path=str(p.relative_to(L)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),frozen_before_read=True)
  # PDF bytes frozen before extraction/reading; no upstream code is executed.
  q=L/'sources'/f'{ident}.txt';c=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,timeout=10);row['pdftotext_exit']=c.returncode;row['pdftotext_stderr']=c.stderr.decode(errors='replace')
 except Exception as e:
  row.update(status='failure',error=repr(e))
  if isinstance(e,urllib.error.HTTPError):
   row['http_status']=e.code
   if e.code in (403,429):stopped=True
  if 'challenge' in str(e).lower():stopped=True
 out.append(row);print(ident,row['status'],flush=True)
 (L/'retained-sources.json').write_text(json.dumps(out,indent=2)+'\n')
(L/'retained-sources.json').write_text(json.dumps(out,indent=2)+'\n')
