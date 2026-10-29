import datetime,hashlib,json,math
from html.parser import HTMLParser
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;S=P.parent/'sol-fresh-source-discovery-r82'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
files={str(p.relative_to(S)):sha(p) for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
(P/'review-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_lane':str(S),'files':files,'credit':0,'counts':[8,38]},indent=2)+'\n')
checks=0
for N in range(2,115,4):
 ps=[]
 for a in range(2,N):
  for b in range(1,a):
   for c in range(1,(N-b)//a+1):
    r=N-a*c
    if r%b==0:ps.append((a,c,b,r//b))
 er=sum((a-c-d)%2==0 for a,c,b,d in ps)
 es=sum((a+b-2*c-d)%2==0 for a,c,b,d in ps)
 countS=sum(a%4==2 and c%2==1 and b%2==1 and d%4==0 and a!=2*b for a,c,b,d in ps)
 m=N//2;ds=[d for d in range(1,m+1) if m%d==0]
 assert er-es==sum(ds)-len(ds)
 assert (es-2*countS)%4==0
 if not any(a*a+b*b==N for a in range(math.isqrt(N)+1) for b in range(math.isqrt(N)+1)):
  assert es%4==(len(ds)%4 if m%4==1 else 0)
 for A,D in [(16,14),(36,30),(72,42),(196,70),(252,114)]:
  if N>=D and (N-D)%A==0:
   assert es%4==0 and (len(ps)-es)%4==0
   if A!=16:assert er%4==0 and (len(ps)-er)%4==0
 checks+=1
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,t):self.parts.append(t)
t=Text();t.feed((S/'sources/dewitt.html').read_text())
text=' '.join(' '.join(t.parts).split())
(P/'source-text.txt').write_text(text+'\n')
idx=text.find('Conjecture 1')
(P/'source-target-excerpt.txt').write_text(text[max(0,idx-900):idx+3800]+'\n')
(P/'ADOPTION.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'Full ordinary proof candidate; independent substantive/source review required','credit':0,'counts':[8,38],'root_read':'Complete proof, summary and discovery. Root reconstructed parity grouping, valuation exchange complement and crossed fixed-point count. Independent final proof gate not claimed.','frozen_files':len(files),'root_bounded_count_checks':checks,'scope':'Entire numbered Conjecture1; later prose residue-zero strengthening not claimed.','strongest_objection':'All main involution/conjugation machinery is already in source; additional divisor/fixed-point arithmetic may be routine. Journal body and current registry holds retained.','proof_sha256':sha(S/'PROOF.md')},indent=2)+'\n')
print(json.dumps({'frozen':len(files),'bounded_checks':checks,'proof_sha256':sha(S/'PROOF.md')}))
print((P/'source-target-excerpt.txt').read_text())
