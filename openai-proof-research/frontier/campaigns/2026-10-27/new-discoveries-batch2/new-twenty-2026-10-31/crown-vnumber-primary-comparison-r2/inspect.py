from pathlib import Path
from html.parser import HTMLParser
import re,json,hashlib
q=Path(__file__).resolve().parent;p=q.parent
class T(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip and d.strip():self.a.append(d.strip())
for f in [q/'http/older-journal.html',p/'crown-vnumber-source-ideation-r1/http/cuts.html',q/'http/older.abs',q/'http/newer.abs',p/'crown-vnumber-source-ideation-r1/http/journal.html']:
 t=T();t.feed(f.read_text());s='\n'.join(t.a);o=q/(f.name+'.txt');o.write_text(s)
 print('FILE',f)
 lines=s.splitlines()
 for i,l in enumerate(lines):
  if re.search('Subscription|subscription|Theorem 4.15|Theorem 3.3|August|July|Published|2026|Correction|corrected|minimal cut|Content available|access to this',l):print(i,repr(' '.join(lines[max(0,i-1):i+3]))[:500])
print('HEADS')
for n in ['openai','pool','omega']:
 s=(q/('http/'+n+'.html')).read_text();print(n,re.findall(r'"currentOid":"([0-9a-f]{40})"',s))
