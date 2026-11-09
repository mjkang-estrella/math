exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text().split("if sys.argv[1]=='extract':")[0],__file__,'exec'))
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','tr','li']:self.a.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.a.append(d)
for r in json.loads((L/'http-receipts.json').read_text()):
 if 'file' not in r:continue
 b=(L/r['file']).read_bytes()
 if b.startswith(b'%PDF'):continue
 p=P();p.feed(b.decode(errors='replace'));txt='\n'.join(' '.join(x.split()) for x in ''.join(p.a).splitlines() if x.strip());put(r['file']+'.txt',txt)
print('converted')
for key in sys.argv[2:]:
 p=L/'sources'/key;lines=p.read_text().splitlines()
 for i,s in enumerate(lines):
  if any(t.lower() in s.lower() for t in ['conjecture','definition 8.','definition 9.','theorem 3.6','theorem 3.8','submission history','journal reference']):print(key,i+1,s[:900])
receipt()
