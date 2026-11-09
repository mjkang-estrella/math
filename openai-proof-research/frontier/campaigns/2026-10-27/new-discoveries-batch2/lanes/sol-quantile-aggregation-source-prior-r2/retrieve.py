import urllib.request,urllib.error,json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**kw): return None
op=urllib.request.build_opener(NoRedirect)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'name':name,'route':'direct HTTPS; redirects disabled; bounded 8MiB/30s'}
 try:
  try: r=op.open(urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'}),timeout=30)
  except urllib.error.HTTPError as e: r=e
  body=r.read(8*1024*1024+1)
  if len(body)>8*1024*1024: raise ValueError('size cap')
  row.update(status=r.code,headers=dict(r.headers),sha256=hashlib.sha256(body).hexdigest(),bytes=len(body))
  (L/(name+'.body')).write_bytes(body)
 except Exception as e: row['error']=str(e)
 with (L/'access.jsonl').open('a') as f: f.write(json.dumps(row)+'\n')
 print(json.dumps(row))
