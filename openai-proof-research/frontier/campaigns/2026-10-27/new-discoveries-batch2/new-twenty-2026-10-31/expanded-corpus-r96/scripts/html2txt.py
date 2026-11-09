import sys,re
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(s):super().__init__();s.parts=[];s.skip=0
 def handle_starttag(s,t,a):
  if t in ['math','script','style']:
   if t=='math':s.parts.append(dict(a).get('alttext',''))
   s.skip+=1
  if t in ['p','div','section','h1','h2','h3','li','blockquote']:s.parts.append('\n')
 def handle_endtag(s,t):
  if t in ['math','script','style']:s.skip-=1
 def handle_data(s,d):
  if not s.skip:s.parts.append(d)
for f in sys.argv[1:]:
 p=P();p.feed(open(f,encoding='utf-8',errors='replace').read());t=re.sub('[ \t]+',' ',' '.join(p.parts));t=re.sub('\n\s*\n+','\n',t)
 open(re.sub(r'\.html$','.txt',f),'w').write(t)
