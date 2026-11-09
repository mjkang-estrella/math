from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,re,sys
R=Path(__file__).resolve().parents[1]; (R/'sources').mkdir(exist_ok=True)
log=json.loads((R/'source-provenance.json').read_text()) if (R/'source-provenance.json').exists() else []
for name,url in [a.split('=',1) for a in sys.argv[1:]]:
 e={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'as served at retrieval'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=25) as f:b=f.read(14000000); e.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  (R/'sources'/name).write_bytes(b);e.update(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
  # detect before any extraction / mathematical use
  low=b[:500000].lower();challenge=any(t in low for t in [b'cf-chl-',b'just a moment...',b'verify you are human',b'proof-of-work',b'captcha',b'anubis_version'])
  e['usable']=not challenge;e['challenge']=challenge
  print(name,e['status'],len(b),'challenge',challenge)
  if challenge: print('STOP challenge; no retry')
 except Exception as ex:e.update(usable=False,error=str(ex)); print(name,'FAIL',str(ex))
 log.append(e); (R/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
