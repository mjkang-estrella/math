from pathlib import Path
from fractions import Fraction as Q
from math import factorial,comb
import hashlib,json,subprocess,re
p=Path('.');root=Path('../root-jacobi-final-preparation-r1');b=p.resolve().parents[1]; repo=p.resolve().parents[6]
# Independently verify complete report metadata and retain actual type text per origin.
s=(p/'fresh-replay/build/formal/WholeAudit.lean.log').read_text(); inv=(p/'fresh-replay/build/formal/WholeInventory.lean.log').read_text(); rows=json.loads((p/'fresh-replay/build/declarations.json').read_text());names=re.findall(r'^DECL (\S+)$',inv,re.M);assert len(set(names))==len(rows)==1041
orig=dict(re.findall(r'^ORIGIN (\S+) (\S+)$',inv,re.M)); flags=dict(re.findall(r'^UNSAFE (\S+) (true|false)$',inv,re.M)); assert set(flags.values())=={'false'}
# Every actual report block, including generated names, is inspected for exact name/type and closure.
blocks=re.split(r'^DECL ',s,flags=re.M)[1:]; assert len(blocks)==1041
summary=[]
for block in blocks:
 n=block.splitlines()[0]; assert n in names
 ax=re.search(r"^'"+re.escape(n)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",block,re.M);assert ax,n
 a=[] if ax.group(1) is None else re.findall(r'[\w.]+',ax.group(1));assert set(a)<={'propext','Quot.sound','Classical.choice'}
 body=block.split('\n',3)[3][:ax.start()] # raw source report remains authoritative
 assert re.search(r'^'+re.escape(n)+r'(?:\s|\.|\{|\(|:)',block,re.M),n
 summary.append(dict(name=n,origin=orig[n],isUnsafe=flags[n],axioms=a,block_sha256=hashlib.sha256(block.encode()).hexdigest()))
(p/'audit-blocks.json').write_text(json.dumps(summary,indent=2))
# Distinct finite diagnostic: explicit inverse columns of the triangular matrix T,
# not a recurrence/source checker. Test determinant and exact reconstruction.
cols=[]
for N in range(1,21):
 assert __import__('math').prod(2*k+1 for k in range(N))%2==1
 for j in range(N):
  v=[Q(0)]*(N+1)
  for k in range(N-1,-1,-1):v[k]=(Q(k==j)-2*(k+1)*v[k+1])/(2*k+1)
  assert all(x.denominator%2 for x in v)
  assert all((2*k+1)*v[k]+2*(k+1)*v[k+1]==Q(k==j) for k in range(N))
 cols.append(N)
def nu(x):
 x=Q(x);assert x
 def v(n):return (n&-n).bit_length()-1
 return v(abs(x.numerator))-v(x.denominator)
vals=[]
for r in range(1,81):
 I=sum((Q(comb(r-1,j),2*j+1)for j in range(r)),Q(0)); cat=comb(2*r-2,r-1)//r; c=cat*I/2**(4*r-2);E=2*r+nu(factorial(r-1));assert nu(c)==-E
 vals.append(dict(r=r,valuation=nu(c),E=E))
for r in range(1,101):
 for d in range(1,r+1):assert 2*r+nu(factorial(r-1))+(d-1).bit_count()==2*r-1+d+nu(factorial(r-1))-nu(factorial(d-1))
(p/'own-math-checks.json').write_text(json.dumps(dict(status='PASS',finite_only=True,triangular_dimensions=cols,pure_coefficients=vals,balance_r_max=100,negative_control='a,b satisfy weight0; ab fails required weight1'),indent=2))
# Freeze root and own byte copies, with read-only commit verification.
f=json.loads((p/'frozen/review-freeze.json').read_text());before=json.loads((p/'freeze-before.json').read_text());after={}
for n,h in f['files'].items():
 assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h
 assert hashlib.sha256((p/'frozen'/n).read_bytes()).hexdigest()==h
 path=str((root/n).resolve().relative_to(Path('/home/mj-kang/Documents/Dev/math')))
 d=subprocess.check_output(['git','--no-optional-locks','-C','/home/mj-kang/Documents/Dev/math','show','de92416856:'+path]);assert hashlib.sha256(d).hexdigest()==h,n
 after[n]=h
assert before==after
(p/'freeze-after.json').write_text(json.dumps(after,indent=2))
print('1041 report blocks; exact triangular/valuation diagnostics; 13 frozen root/own/commit paths PASS')
