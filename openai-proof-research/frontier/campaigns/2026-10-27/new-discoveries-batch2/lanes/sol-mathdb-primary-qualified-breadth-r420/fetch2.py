from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,re
W=Path(__file__).resolve().parent;E=W/'evidence';E.mkdir(exist_ok=True)
items=[('owr730-pdf','https://ems.press/content/serial-article-files/45933?nt=1'),('owr742-pdf','https://ems.press/content/serial-article-files/45958?nt=1'),('owr711-pdf','https://ems.press/content/serial-article-files/45848?nt=1')];blocked=set();out=[]
for key,url in items:
 host=urllib.parse.urlparse(url).netloc
 if host in blocked:out.append({'key':key,'url':url,'result':'not_attempted_host_stop'});continue
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=30) as r:
   b=r.read(18000000);code=r.status;final=r.url
  (E/(key+'.body')).write_bytes(b);d={'key':key,'url':url,'final_url':final,'status':code,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};out.append(d)
  if key.startswith('owr'):
   s=b.decode(errors='replace'); links=re.findall(r'(?:href|src)=[\"\']([^\"\']+)',s);print(key,[a for a in links if 'content/' in a or '.pdf' in a])
 except Exception as e:
  out.append({'key':key,'url':url,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:blocked.add(host)
(E/'fetch2-log.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
