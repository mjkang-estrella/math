import pathlib,json,hashlib,subprocess,re,html
D=pathlib.Path(__file__).resolve().parents[1];A=D.parent/'expanded-corpus-r250'; out={}
for v in range(1,6):
 p=A/'sources'/f'1601.08199v{v}.pdf';r=json.loads(p.with_suffix('.pdf.receipt.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];dest=D/'receipts'/f'v{v}-independent.txt';subprocess.run(['pdftotext','-layout',str(p),str(dest)],check=True);s=dest.read_text(); key='Conjecture 13.' if v in [2,3] else 'Conjecture 2.5.';i=s.find(key);out[str(v)]={'receipt':r,'conjecture_context':s[max(0,i-300):i+1250] if i>=0 else 'not present','parallel_contexts':[s[max(0,m.start()-100):m.end()+100] for m in re.finditer('parallel',s)],'simple_occurrences':[s[max(0,m.start()-80):m.end()+80] for m in re.finditer(r'\bsimple\b',s)]}
p=A/'sources/lason-journal.html';r=json.loads(p.with_suffix('.html.receipt.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):self.a.append(d)
p1=P();p1.feed(p.read_text());s=' '.join(p1.a);(D/'receipts/journal-independent.txt').write_text(s);i=s.find('Conjecture 2.5');out['journal']={'receipt':r,'context':s[i-200:i+1900],'parallel_contexts':[s[max(0,m.start()-80):m.end()+100] for m in re.finditer('parallel',s)]}
(D/'receipts/source-read.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v.get('context',v.get('conjecture_context')) for k,v in out.items()},indent=2))
