import pathlib,json,urllib.request,urllib.error,datetime,hashlib,subprocess,time
D=pathlib.Path(__file__).resolve().parent;(D/'sources').mkdir(exist_ok=True)
rows=json.loads((D/'assigned-records.json').read_text());done=set();blocked=False
with (D/'sources.jsonl').open('x') as log:
 for r in rows:
  url=r['record']['source_url']; aid=url.rsplit('/',1)[-1]
  if aid in done:continue
  done.add(aid);u='https://arxiv.org/pdf/'+aid
  entry={'url':u,'recorded_source_url':url,'version':'current arXiv PDF; exact version requires title-page inspection','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'ids':[x['record']['mathdb_id'] for x in rows if x['record']['source_url']==url]}
  if blocked:entry['status']='HOLD inherited access stop for arxiv.org; not attempted'
  else:
   try:
    req=urllib.request.Request(u,headers={'User-Agent':'MathResearchScreen/1.0 (bounded scholarly source reading)'})
    with urllib.request.urlopen(req,timeout=12) as res:
     b=res.read(12000001);entry['http_status']=res.status;entry['final_url']=res.url
    assert len(b)<=12000000,'response cap';assert b.startswith(b'%PDF'),'not PDF or challenge'
    p=D/'sources'/(aid+'.pdf');p.write_bytes(b);entry.update(file=str(p.relative_to(D)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),status='retained_not_yet_read')
    out=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True,timeout=12);entry['pdftotext_exit']=out.returncode;entry['pdftotext_stderr']=out.stderr
   except urllib.error.HTTPError as e:
    entry.update(status='HOLD_HTTP',http_status=e.code,error=str(e))
    if e.code in (403,429):blocked=True
   except Exception as e:entry.update(status='HOLD_ERROR',error=repr(e));blocked='challenge' in str(e)
   time.sleep(.3)
  log.write(json.dumps(entry)+'\n');log.flush();print(aid,entry['status'],flush=True)
