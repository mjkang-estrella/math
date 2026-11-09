from pathlib import Path
import urllib.request,urllib.parse,hashlib,json,datetime,sys
L=Path(__file__).resolve().parent
url=sys.argv[1];name=sys.argv[2]
assert not any(x in url.lower() for x in ['google','sciencedirect','api.github','raw.githubusercontent','codeload','/diff','/patch'])
p=L/'sources'/name;p.parent.mkdir(exist_ok=True)
log=L/'access.json';a=json.loads(log.read_text()) if log.exists() else []
entry=dict(url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat(),file=str(p.relative_to(L)))
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceCheck/1.0'}),timeout=35) as r:
  data=r.read(12*1024*1024);entry.update(status=r.status,sha256=hashlib.sha256(data).hexdigest(),size=len(data))
 p.write_bytes(data)
except Exception as e:entry['failure']=str(e)
a.append(entry);log.write_text(json.dumps(a,indent=2)+'\n');print(entry)
