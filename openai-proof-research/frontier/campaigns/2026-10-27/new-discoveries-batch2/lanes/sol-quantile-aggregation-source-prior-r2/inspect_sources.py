import json,hashlib,subprocess,re,html,base64
from pathlib import Path
L=Path(__file__).resolve().parent
for n in ['accepted','extremes','systemic','joint','robust']:
 p=L/(n+'.body')
 if p.exists() and p.read_bytes().startswith(b'%PDF') and not (L/(n+'.txt')).exists():
  subprocess.run(['pdftotext','-layout',str(p),str(L/(n+'.txt'))],check=True)
  with (L/'derived.jsonl').open('a') as f:f.write(json.dumps({'file':n+'.txt','sha256':hashlib.sha256((L/(n+'.txt')).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'method':'pdftotext -layout'})+'\n')
if (L/'joint-search.body').exists():
 s=(L/'joint-search.body').read_text()
 for chunk in re.findall(r'<li class="b_algo".*?</li>',s,re.S):
  print(re.sub('<[^>]+>',' ',html.unescape(chunk))[:1200])
  for url in re.findall(r'href="([^"]+)"',chunk):
   url=html.unescape(url)
   if 'u=a1' in url:
    enc=url.split('u=a1')[1].split('&')[0]
    try:url=base64.b64decode(enc+'='*((-len(enc))%4)).decode()
    except Exception:pass
   print(url)
if (L/'robust-query.body').exists():
 import xml.etree.ElementTree as E
 r=E.fromstring((L/'robust-query.body').read_bytes()); ns={'a':'http://www.w3.org/2005/Atom'}
 for e in r.findall('a:entry',ns): print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
