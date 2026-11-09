import urllib.request,urllib.error,json,hashlib,datetime,sys
from pathlib import Path
P=Path(__file__).parent; log=P/'retrievals.json'
rows=json.loads(log.read_text()) if log.exists() else []
blocked={r['host'] for r in rows if r.get('status') in [403,429] or r.get('challenge')}
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 host=urllib.parse.urlsplit(url).hostname
 if host in blocked: raise SystemExit('Host blocked earlier: '+host)
 r={'file':name,'url':url,'host':host,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=40) as f: data=f.read(15000000);r['status']=f.status
  r['sha256']=hashlib.sha256(data).hexdigest();r['bytes']=len(data)
  if b'Just a moment...' in data[:10000] or b'cf-chl-' in data[:10000]:r['challenge']=True;blocked.add(host)
  else:(P/'sources'/name).write_bytes(data)
 except urllib.error.HTTPError as e:
  r['status']=e.code
  if e.code in [403,429]:blocked.add(host)
 except Exception as e:r['error']=str(e)
 rows.append(r);log.write_text(json.dumps(rows,indent=2));print(r)
