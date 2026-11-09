from html.parser import HTMLParser
import pathlib,json,re
P=pathlib.Path(__file__).resolve().parents[1]
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.stack=[];self.text=[];self.cs=[];self.active=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math':self.text.append(' $'+a.get('alttext','')+'$ ');self.math+=1
  if t in ['script','style']:self.skip+=1
  if 'ltx_theorem' in a.get('class',''):self.active.append((len(self.stack),len(self.text),a.get('id')))
  if t not in ['meta','link','img','br','hr','input','source','wbr']:self.stack.append(t)
 def handle_endtag(self,t):
  if t=='math':self.math=max(0,self.math-1)
  if t in ['script','style']:self.skip=max(0,self.skip-1)
  if t in self.stack:
   depth=len(self.stack)-1-self.stack[::-1].index(t)
   while self.active and self.active[-1][0]>=depth:
    _,start,id=self.active.pop();st=' '.join(self.text[start:]);
    if re.search('conjecture',st[:180],re.I):self.cs.append({'id':id,'text':st})
   self.stack=self.stack[:depth]
 def handle_data(self,d):
  if not self.math and not self.skip and d.strip():self.text.append(d.strip())
out={}
for f in sorted((P/'sources').glob('26*.html')):
 s=Parser();s.feed(f.read_text());(P/'sources'/f'{f.stem}.txt').write_text(' '.join(s.text));out[f.stem]=s.cs
(P/'outputs/source-conjectures.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for k,v in out.items():
 print('\nSOURCE',k)
 for c in v:print(c['id'],c['text'][:3500])
