import pathlib,urllib.request,urllib.error,hashlib,datetime,json,subprocess
D=pathlib.Path(__file__).resolve().parent;stop=False
with (D/'successor-bodies.jsonl').open('x') as log:
 for aid in ['1911.11252v3','2006.15287v5','2205.06033v3','2004.12871v2']:
  u='https://arxiv.org/pdf/'+aid;r={'url':u,'version':aid,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
  if stop:r['status']='HOLD not attempted after access stop'
  else:
   try:
    with urllib.request.urlopen(u,timeout=15) as response:b=response.read(12000001)
    assert b.startswith(b'%PDF') and len(b)<=12000000
    p=D/'sources'/(aid+'.pdf');p.write_bytes(b);r.update(file=str(p.relative_to(D)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),status='retained_not_yet_read')
    s=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True,timeout=15);r['pdftotext_exit']=s.returncode;r['stderr']=s.stderr
   except urllib.error.HTTPError as e:r.update(status='HOLD_HTTP',error=str(e),http_status=e.code);stop=e.code in (403,429)
   except Exception as e:r.update(status='HOLD_ERROR',error=repr(e))
  log.write(json.dumps(r)+'\n');log.flush();print(aid,r['status'])
