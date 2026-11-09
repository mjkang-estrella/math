from pathlib import Path
import urllib.request,urllib.error,urllib.parse,hashlib,json,datetime
R=Path(__file__).resolve().parents[1];logs=[];stopped=set()
urls=[('mmwave-current','https://arxiv.org/abs/1901.01894'),('subgroups-current','https://arxiv.org/abs/2411.02219'),('trees-current','https://arxiv.org/abs/0906.2183'),('mmwave-search','https://www.bing.com/search?q='+urllib.parse.quote('"1901.01894" "conjecture"')),('trees-search','https://www.bing.com/search?q='+urllib.parse.quote('"tree polynomials" "Conjecture 3.17"'))]
for name,url in urls:
 host=urllib.parse.urlparse(url).netloc
 if host in stopped:continue
 e=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version='current HTTP snapshot');logs.append(e)
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read(5000000);e.update(status=f.status,final_url=f.url)
 except urllib.error.HTTPError as ex:
  b=ex.read();e.update(status=ex.code,failure=str(ex));stopped.add(host)
 except Exception as ex:e['failure']=str(ex);stopped.add(host);b=b''
 p=R/'sources'/f'{name}.html';p.write_bytes(b);e.update(path=str(p.relative_to(R)),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 if any(w in b.lower() for w in [b'captcha',b'challenge-platform',b'verify you are human']):e['challenge_marker']=True;stopped.add(host)
 (R/'successor-provenance.json').write_text(json.dumps(logs,indent=2)+'\n')
print(json.dumps(logs,indent=2))
