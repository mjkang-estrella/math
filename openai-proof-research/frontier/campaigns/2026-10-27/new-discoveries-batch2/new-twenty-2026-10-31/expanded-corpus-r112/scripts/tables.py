# Extract numeric tables from the arXiv HTML of 2604.16188 (diagnostic transcription only).
import re,sys,html
from html.parser import HTMLParser
src=open(sys.argv[1]).read()
class T(HTMLParser):
    def __init__(s):
        super().__init__();s.tables=[];s.cur=None;s.row=None;s.cell=None;s.depth=0;s.cap=None;s.incap=False
    def handle_starttag(s,t,a):
        a=dict(a)
        if t=='table': s.depth+=1; 
        if t=='table' and s.depth==1: s.cur=[];
        if t=='tr' and s.cur is not None: s.row=[]
        if t in('td','th') and s.row is not None: s.cell=''
        if t=='math' and s.cell is not None: s.cell+=a.get('alttext','')+' '
        if t=='figcaption': s.incap=True; s.cap=''
    def handle_endtag(s,t):
        if t in('td','th') and s.row is not None and s.cell is not None: s.row.append(s.cell.strip()); s.cell=None
        if t=='tr' and s.cur is not None and s.row is not None: s.cur.append(s.row); s.row=None
        if t=='table':
            s.depth-=1
            if s.depth==0 and s.cur is not None: s.tables.append([None,s.cur]); s.cur=None
        if t=='figcaption':
            s.incap=False
            if s.tables and s.tables[-1][0] is None: s.tables[-1][0]=s.cap
            else: s.pending=s.cap
    def handle_data(s,d):
        if s.incap: s.cap+=d
p=T();p.feed(src)
want=sys.argv[2:] 
for cap,rows in p.tables:
    c=(cap or '')
    m=re.search(r'Table (\d+)',c)
    if want and (not m or m.group(1) not in want): continue
    print('=== ',c.strip()[:150])
    for r in rows: print(' | '.join(x.replace('$','').strip() for x in r))
