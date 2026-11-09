from pathlib import Path
import json
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self): super().__init__(); self.parts=[]; self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'): self.skip+=1
 def handle_endtag(self,t):
  if t in ('script','style'): self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
L=Path(__file__).resolve().parents[1]
for p in (L/'receipts').glob('*.json'):
 try:
  r=json.loads(p.read_text()); b=L/'receipts'/r['body']; data=b.read_bytes()
  if b'<html' in data[:3000].lower() or b'<!doctype html' in data[:3000].lower():
   s=P(); s.feed(data.decode(errors='replace')); (L/'inputs'/(b.stem+'.txt')).write_text(' '.join(s.parts))
 except (KeyError,TypeError): pass
