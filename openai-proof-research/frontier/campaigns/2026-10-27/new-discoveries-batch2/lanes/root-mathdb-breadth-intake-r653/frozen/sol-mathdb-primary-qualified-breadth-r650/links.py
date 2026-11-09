import pathlib,json,hashlib
from html.parser import HTMLParser
D=pathlib.Path(__file__).resolve().parent
class P(HTMLParser):
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='a' and ('pdf' in a.get('href','').lower() or '/abs/' in a.get('href','')): print(a.get('href'))
for r in json.loads((D/'source-provenance.json').read_text()):
 if 'path' not in r:continue
 b=pathlib.Path(r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'];print(r['name']);P().feed(b.decode())
