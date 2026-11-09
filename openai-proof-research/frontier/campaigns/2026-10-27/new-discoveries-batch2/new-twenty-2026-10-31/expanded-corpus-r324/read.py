from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','section','div','h1','h2','h3','h4','li']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,s):
  if not self.skip:self.parts.append(s)
for l in (P/'http-receipts.jsonl').read_text().splitlines():
 r=json.loads(l)
 if 'file' not in r:continue
 f=P/r['file']; textfile=f.with_suffix('.txt')
 parser=Text();parser.feed(f.read_text(errors='replace'));t=''.join(parser.parts);textfile.write_text(t)
 if len(sys.argv)>2 and sys.argv[2] not in r['url']:continue
 print('\nURL',r['url'])
 if len(sys.argv)>3:
  for term in sys.argv[3:]:
   pos=0;count=0
   while count<12:
    pos=t.lower().find(term.lower(),pos)
    if pos<0:break
    print(t[max(0,pos-500):pos+3000]);pos+=len(term);count+=1
 else:print(t[:18000])
