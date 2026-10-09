from pathlib import Path
from html.parser import HTMLParser
import hashlib,json,re
S=Path(__file__).resolve().parents[2]/'sources/i21_signed_saxl_dominance'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.skip=0;self.math=0;self.out=[]
 def handle_starttag(self,t,a):
  a=dict(a)
  if t in ('script','style'):self.skip+=1
  if self.skip:return
  if t=='math':self.math+=1;self.out.append(' $'+a.get('alttext','')+'$ ')
  if not self.math and t in ('p','h1','h2','h3','h4','h5','div','tr'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
  if t=='math':self.math-=1
 def handle_data(self,s):
  if not self.skip and not self.math:self.out.append(s)
p=Parser();p.feed((S/'literature/bb-v3.html').read_text());t='\n'.join(' '.join(x.split()) for x in ''.join(p.out).splitlines() if x.strip());(S/'bb-readable.txt').write_text(t)
contracts=[]
for label in ['Lemma 2.1.','Lemma 2.3.','Lemma 2.4.','Proposition 2.5.','Theorem 3.7.','Theorem 5.2.','Theorem 6.1.','Corollary 6.2.','Theorem 6.3.','Theorem 7.8.','Theorem 7.11.','Theorem 7.15.','Conjecture 10.1.','Conjecture 10.2.']:
 a=t.index(label);tail=t[a+len(label):];matches=list(re.finditer(r'\n(?:Proof\.|(?:Theorem|Lemma|Proposition|Corollary|Conjecture|Remark)s? \d+\.\d+\.)',tail));b=a+len(label)+matches[0].start() if matches else len(t)
 block=t[a:b];contracts.append(dict(file='bb-readable.txt',label=label,start_offset=a,end_offset=b,sha256=sha(block.encode()),text=block))
# Explicit proof read ranges, not claims to have read all retained literature.
primary=[]
for file,start,end,purpose in [('bb-readable.txt',44000,48102,'Definitions, flip character identities and symmetric semigroup'),('bb-readable.txt',60000,62300,'Known staircase diagonal splitting'),('bb-readable.txt',78882,82819,'Proof of the three uniform exterior exceptions'),('bb-readable.txt',97400,107000,'Alternating-group restriction, sign and near-sign proofs'),('bb-readable.txt',152000,152900,'Almost-balanced two-row splitting'),('bb-readable.txt',157000,161560,'Known two-row exterior vanishing'),('bb-readable.txt',170000,175054,'Exact Conjectures 10.1–10.3 and small-size context')]:
 txt=(S/file).read_text();end=min(end,len(txt));primary.append(dict(file=file,start_offset=start,end_offset=end,sha256=sha(txt[start:end].encode()),purpose=purpose))
for file,intervals in [('literature/ikenmeyer-v2.txt',[(85,122),(260,412)]),('literature/critical-v1.txt',[(45,260)])]:
 lines=(S/file).read_text().splitlines(keepends=True)
 for a,b in intervals:
  block=''.join(lines[a-1:b]);primary.append(dict(file=file,start_line=a,end_line=b,sha256=sha(block.encode()),purpose='Dominance construction / classical alternating-group split comparison'))
write(S/'primary-contracts.json',contracts);write(S/'primary-read-passages.json',primary)
reads=[]
for manuscript,names in [('A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026',['dominance','band-quotient','path-band','specht-tools','completion']),('Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026',['balance','band','candidate','completion'])]:
 for name in names:
  f=f'preprints/{manuscript}/build/sections/{name}.tex';b=(S/'pinned'/f).read_bytes();reads.append(dict(path=f,start_line=1,end_line=len(b.decode().splitlines()),sha256=sha(b),read='full statement and proof'))
for name,end in [('introduction',150),('preliminaries',120)]:
 f=f'preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/build/sections/{name}.tex';b=''.join((S/'pinned'/f).read_text().splitlines(keepends=True)[:end]);reads.append(dict(path=f,start_line=1,end_line=end,sha256=sha(b.encode()),read='selected contracts and comparison'))
write(S/'source-read-passages.json',reads)
write(S/'literature/versions.json',dict(checked='2026-10-09',bb=dict(arxiv='2202.03066v3',version_date='2023-01-18',published='2023-08-29',doi='10.5802/alco.294',retained_i19_bytes_equal=(S/'literature/bb-v3.html').read_bytes()==(S/'inputs/frontier/sources/i19_fresh_structural_discovery/literature/bessenrodt-bowman.html').read_bytes()),ikenmeyer=dict(arxiv='1410.6549v2',version_date='2015-05-05'),bessenrodt_critical=dict(arxiv='1704.00707v1',version_date='2017-04-03',doi='10.5802/alco.18'),limit='Bounded current search, not an assertion of worldwide priority or exhaustive literature coverage.'))
