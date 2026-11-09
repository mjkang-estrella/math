from pathlib import Path
import json,hashlib,zipfile,stat,shutil
import sympy as S
root=Path(__file__).resolve().parents[1]; b=root.parent
m,y,t=S.symbols('m y t')
def tau(n,i):
 if i==0:return S.Integer(1)
 return S.expand(4**i*n**2*S.prod(n**2-a*a for a in range(1,i))/S.factorial(2*i))
def Tcoeff(i,E):
 e=i//2;j=E-e
 if j<0:return 0
 if i%2==0:return tau(m+e,j)
 return (tau(m+e+1,j)-tau(m+e,j))/2
A={E:S.expand(sum(tau(m,i)*Tcoeff(i,E) for i in range(2*E+1))) for E in range(1,4)}
R=[S.expand(sum((-1)**(F+1-E)*A[E] for E in range(1,F+2))) for F in range(3)]
assert S.expand(R[0]-S.Rational(2,3)*m*m*(m+1)*(m+5))==0
P1=2*m**8+56*m**7+476*m**6+1400*m**5+938*m**4-1456*m**3-1416*m**2
P2=4*m**12+264*m**11+6380*m**10+71280*m**9+379302*m**8+820512*m**7-183040*m**6-3127080*m**5-2604206*m**4+2235024*m**3+2401560*m**2
assert S.expand(315*R[1]-P1)==0
assert S.expand(467775*R[2]-P2)==0
cert=[]
for q,s,mod in [(4,3,128),(16,15,256),(16,11,256)]:
 for j,P in enumerate([P1,P2],1):
  if s==11 and j==2:continue
  coeff=[int(S.expand(P.subs(m,q*t+s)).coeff(t,i)) for i in range(S.degree(P,m)+1)]
  rem=[c%mod for c in coeff]
  assert rem==([128]+[0]*(len(coeff)-1) if s==11 else [0]*len(coeff))
  cert.append(dict(q=q,s=s,polynomial=j,modulus=mod,coefficients=coeff,residues=rem))
(root/'low-coefficient-certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
def coeffs(m,N):
 a=[1]+[0]*N
 sizes=[1,1];s=2
 while s<=N:sizes.append(s);s*=2
 for s in sizes:
  for _ in range(m):
   for n in range(s,N+1):a[n]+=a[n-s]
 return a
examples=[]
for mm,nn in [(1,1),(2,1),(3,1),(3,2),(4,1),(7,1),(11,2),(15,1)]:
 a=coeffs(mm,4*nn);d=a[4*nn]-a[nn];v=(d&-d).bit_length()-1
 examples.append(dict(m=mm,n=nn,c_n=a[nn],c_4n=a[4*nn],difference=d,valuation=v))
(root/'examples.json').write_text(json.dumps(examples,indent=2)+'\n')
s=(root/'paper.md').read_text()
start=s.index('[TABLE]');end=s.index('[/TABLE]',start)+len('[/TABLE]')
rows=['[TABLE]','m | n | Δ_m(n) | ν₂(Δ_m(n)) | relevant lower target']
for a in examples:
 mm,nn=a['m'],a['n'];vn=(nn&-nn).bit_length()-1
 target=vn+((2*((mm//2 & -(mm//2)).bit_length()-1)+3) if mm%2==0 else (3 if mm%4==1 else 6))
 rows.append(f"{mm} | {nn} | {a['difference']} | {a['valuation']} | {target}")
rows.append('[/TABLE]');s=s[:start]+'\n'.join(rows)+s[end:];(root/'paper.md').write_text(s)
archive=b/'ulas-assembly-r1/ulas-source.zip'
assert hashlib.sha256(archive.read_bytes()).hexdigest()=='bafc3b63f6baba271680f2eed29334603149cee7c17a714bb7b4b1a04c37d3a1'
shutil.copyfile(archive,root/'ulas-source.zip')
target=root/'safe-extraction';target.mkdir(exist_ok=True)
entries=[]
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 for item in z.infolist():
  path=Path(item.filename)
  assert not path.is_absolute() and '..' not in path.parts and not stat.S_ISLNK(item.external_attr>>16)
  assert item.file_size<100*1024**2
  dst=target/path;assert dst.resolve().is_relative_to(target.resolve())
  if item.is_dir():dst.mkdir(parents=True,exist_ok=True);continue
  dst.parent.mkdir(parents=True,exist_ok=True);data=z.read(item);dst.write_bytes(data)
  entries.append(dict(path=item.filename,size=len(data),sha256=hashlib.sha256(data).hexdigest()))
(root/'receipts/safe-extraction.json').write_text(json.dumps(dict(archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),crc_ok=True,lean_run=False,files=entries),indent=2)+'\n')
print('Exact symbolic identities, residue certificates, examples, and safe extraction passed.')
print(examples)
