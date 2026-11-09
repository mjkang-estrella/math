import os, resource
os.sched_setaffinity(0, {0, 1})
resource.setrlimit(resource.RLIMIT_CPU, (110, 110))
resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
import pathlib, json, hashlib, time, atexit, sys, re, html.parser, urllib.request, datetime
L = pathlib.Path(__file__).parent
START = time.monotonic()
READS = []
def read(p):
    b = p.read_bytes()
    READS.append({'path': str(p), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
    return b.decode()
def done():
    p = L / 'process-inventory.json'
    v = json.loads(p.read_text())
    v.append({'command': sys.argv, 'pid': os.getpid(), 'affinity_set': [0,1], 'CPU_cap_s':110, 'AS_cap_bytes':2147483648, 'wall_cap_s':125, 'elapsed_s':time.monotonic()-START, 'usage':list(resource.getrusage(resource.RUSAGE_SELF)), 'reads':READS, 'completion':'atexit; shell/tool must confirm reaped exit'})
    p.write_text(json.dumps(v,indent=2)+'\n')
atexit.register(done)
class Parser(html.parser.HTMLParser):
    def __init__(self): super().__init__(); self.o=[]; self.math=0; self.skip=0
    def handle_starttag(self,t,a):
        a=dict(a)
        if t=='math': self.o.append(' '+a.get('alttext','')+' '); self.math+=1
        if t in ['script','style']: self.skip+=1
        if t in ['p','section','h1','h2','h3','h4','li','figure','div']: self.o.append('\n')
    def handle_endtag(self,t):
        if t=='math': self.math-=1
        if t in ['script','style']: self.skip-=1
    def handle_data(self,d):
        if not self.math and not self.skip: self.o.append(d)
def parse(s):
    p=Parser();p.feed(s)
    return re.sub(r'\n\s*\n+', '\n\n', re.sub(r'[ \t]+',' ',''.join(p.o)))
if sys.argv[1]=='parse':
    for p in sorted((L/'sources').glob('*.html')):
        (p.with_suffix('.txt')).write_text(parse(read(p)))
    print('Parsed cached HTML; this does not assert cognitive full-body review.')
elif sys.argv[1]=='excerpt':
    s=read(L/'sources'/sys.argv[2]); term=sys.argv[3]; hits=list(re.finditer(term,s,re.I)); print('offsets',[m.start() for m in hits]);
    for m in hits[:int(sys.argv[4])]: print(s[max(0,m.start()-200):m.start()+int(sys.argv[5])])
elif sys.argv[1]=='slice':
    s=read(L/'sources'/sys.argv[2]);print(s[int(sys.argv[3]):int(sys.argv[4])])
elif sys.argv[1]=='fetch':
    receipts=json.loads((L/'http-receipts.json').read_text())
    for name,url in zip(sys.argv[2::2],sys.argv[3::2]):
        rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
        try:
            with urllib.request.urlopen(url,timeout=15) as f:
                b=f.read(16000000);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(L/'sources'/f'{name}.html').write_bytes(b)
        except Exception as e:rec.update(error=str(e),status=getattr(e,'code',None))
        receipts.append(rec); print(rec)
    (L/'http-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
