import pathlib,json,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class Parser(HTMLParser):
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='a' and ('pdf' in d.get('href','') or 'download' in d.get('href','')):print(d.get('href'))
for e in json.loads((P/'fetch-provenance.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];print(e['path']);Parser().feed(b.decode())
