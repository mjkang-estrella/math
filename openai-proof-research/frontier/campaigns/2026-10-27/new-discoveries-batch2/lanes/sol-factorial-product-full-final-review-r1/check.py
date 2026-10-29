from pathlib import Path
import hashlib,json,zipfile,sys,math
from fractions import Fraction
L=Path(__file__).resolve().parent
B=L.parent; T=B/'sol-factorial-product-manuscript-packet-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
F=B/'root-factorial-final-review-freeze-r1/freeze.json'
def freeze(tag):
 d=json.loads(F.read_text()); rows={n:{'expected':h,'actual':sha(T/n)} for n,h in d['files'].items()}
 assert all(v['expected']==v['actual'] for v in rows.values())
 rows['DESCRIPTOR']={'actual':sha(F)}
 (L/f'freeze-{tag}.json').write_text(json.dumps(rows,indent=2)+'\n')
 return rows
if sys.argv[1]=='before':
 freeze('before')
 with zipfile.ZipFile(T/'packet.zip') as z:
  assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
  z.extractall(L/'extracted')
elif sys.argv[1]=='after':
 assert freeze('after')==json.loads((L/'freeze-before.json').read_text())
else:
 A=[3,5,6,7,8,14,16,20,36];Bv=[4,10,12,15,18,21,32]
 P=[p for p in range(2,37) if all(p%d for d in range(2,math.isqrt(p)+1))]
 def vp(n,p):
  e=0
  while n%p==0:n//=p;e+=1
  return e
 def val(t,p):
  q=p;s=0
  while q<=t:s+=t//q;q*=p
  return s-t*vp(t,p)
 rows=[[val(t,p) for p in P] for t in A+Bv]
 for t,row in zip(A+Bv,rows):
  q=Fraction(math.factorial(t),t**t)
  assert row==[vp(q.numerator,p)-vp(q.denominator,p) for p in P]
 c=json.loads((L/'extracted/certificate.json').read_text())
 assert c['rows']==rows and c['primes']==P
 totals=[[sum(r[j] for r in rs) for j in range(len(P))] for rs in [rows[:9],rows[9:]]]
 assert totals[0]==totals[1]==[-123,-37,-4,-8,6,5,3,2,1,1,1]
 assert c['totals']==totals
 assert len(set(A+Bv))==16 and min(A+Bv)>1
 x=math.prod(Fraction(math.factorial(t),t**t) for t in A)
 y=math.prod(Fraction(math.factorial(t),t**t) for t in Bv)
 assert x==y
 numA=math.prod(math.factorial(t) for t in A);denA=math.prod(t**t for t in A)
 numB=math.prod(math.factorial(t) for t in Bv);denB=math.prod(t**t for t in Bv)
 assert numA*denB==numB*denA
 out={'status':'PASS','entries':176,'A':A,'B':Bv,'primes':P,'rows':rows,'totals':totals,'rational':[x.numerator,x.denominator],'integer_crossproduct':str(numA*denB),'certificate_matches':True}
 (L/'exact-receipt.json').write_text(json.dumps(out,indent=2)+'\n')
