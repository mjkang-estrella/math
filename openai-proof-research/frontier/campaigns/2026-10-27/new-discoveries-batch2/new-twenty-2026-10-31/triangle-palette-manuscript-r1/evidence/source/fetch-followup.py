import urllib.request, urllib.error, json, hashlib, datetime, concurrent.futures
from pathlib import Path
r=Path(__file__).parent
urls={'omega-root':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/28be449e222312b52adb0b4fad8742c6fc16bd5e','colourblind':'https://home.agh.edu.pl/~pilsniak/16.pdf','full-neighbor':'https://home.agh.edu.pl/~pilsniak/39.pdf','quasi-majority':'https://home.agh.edu.pl/~pilsniak/59.pdf'}
def get(pair):
 name,url=pair;d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=25) as q: b=q.read();d.update(status=q.status,final_url=q.url)
 except urllib.error.HTTPError as e:b=e.read();d.update(status=e.code,final_url=e.url)
 except Exception as e:b=b'';d.update(error=repr(e))
 (r/(name+'.body')).write_bytes(b);d.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(r/(name+'.receipt.json')).write_text(json.dumps(d,indent=2));return name,d
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for name,d in pool.map(get,urls.items()):print(name,json.dumps(d))
