from research import H
from html.parser import HTMLParser
import subprocess
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t=='math':
   d=dict(a)
   if 'alttext' in d:self.a.append(' '+d['alttext']+' ')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
  if t in ['p','div','section','h2','h3','h4','li']:self.a.append('\n')
 def handle_data(self,s):
  if not self.skip:self.a.append(s)
for n in ['domino','partite','domino-versions','partite-versions']:
 p=Parser();p.feed((H/'sources'/f'{n}.html').read_text());(H/'sources'/f'{n}.txt').write_text(''.join(p.a))
subprocess.run(['pdftotext','-layout',str(H/'sources/spectral.pdf'),str(H/'sources/spectral.txt')],check=True)
