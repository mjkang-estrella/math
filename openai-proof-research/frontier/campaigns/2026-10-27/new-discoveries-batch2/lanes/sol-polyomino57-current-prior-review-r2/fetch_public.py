from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,concurrent.futures,re
D=Path(__file__).resolve().parent
(D/'sources').mkdir(exist_ok=True)
def get(item):
 name,url,limit=item; row={'url':url,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=45) as r:
   row.update(status=r.status,final_url=r.url,headers=dict(r.headers)); data=r.read(limit+1)
   if len(data)>limit: row.update(error='bounded download limit exceeded; body not complete',bytes_read=len(data))
   else:
    p=D/'sources'/name;p.write_bytes(data);row.update(path=str(p.relative_to(D)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    if name.endswith('.html'):row['currentOid']=sorted(set(re.findall(r'"currentOid":"([0-9a-f]{40})"',data.decode(errors='replace'))))
 except Exception as e:row['error']=str(e)
 row['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();return row
if __name__=='__main__':
 items=[('omega-current.html','https://github.com/the-omega-institute/trureturing',1500000),('openai-current.html','https://github.com/openai/math',1500000),('aim-current.html','https://github.com/MColbrook/AIM',1500000),('count-current.html','https://github.com/suvrit/count-ex-machina',1500000)]
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as x: rows=list(x.map(get,items))
 (D/'http-current.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
