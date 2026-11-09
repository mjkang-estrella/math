from html.parser import HTMLParser
from pathlib import Path
import sys,base64
class P(HTMLParser):
 def handle_starttag(self,t,a):
  if t=='a':
   h=dict(a).get('href','')
   if 'a1' in h and 'u=' in h:
    try:h=base64.b64decode(h.split('u=a1')[1].split('&')[0]+'===').decode()
    except Exception:pass
   if h.startswith('http'):print('\nLINK',h)
 def handle_data(self,d):
  if d.strip():print(d.strip()[:1400])
P().feed(Path(sys.argv[1]).read_text())
