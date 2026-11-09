import os,pathlib,hashlib,json,zipfile,stat
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
O=pathlib.Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
expected='987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175'
assert sha(O/'lean-source.zip')==expected
with zipfile.ZipFile(O/'lean-source.zip') as z:
 names=set();total=0
 for x in z.infolist():
  p=pathlib.PurePosixPath(x.filename);mode=x.external_attr>>16
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in x.filename and x.filename not in names
  assert not stat.S_ISLNK(mode) and (not stat.S_IFMT(mode) or stat.S_ISREG(mode) or stat.S_ISDIR(mode))
  assert x.file_size<16*1024**2 and p.suffix not in ['.olean','.ilean','.so'];names.add(x.filename);total+=x.file_size
  assert total<64*1024**2
  if not x.is_dir():assert (O/'packet-extracted'/x.filename).read_bytes()==z.read(x)
assert len(list((O/'packet-extracted').glob('*.lean')))==54
for r in json.loads((O/'receipts/source-copies.json').read_text()):assert sha(O/r['copy'])==r['sha256']
raw=(O/'mathdb-354228.raw.jsonl').read_bytes();assert raw.endswith(b'\n');json.loads(raw)
def label(t,n,h,i):
 if n==1:return i+1
 if n==2:
  if t==2:return ([1,4] if h==1 else [2,3,6,5])[i]
  s=t//2
  if h==1:return 2 if i==0 else 3*s+2-i
  p,j=divmod(i,t)
  if p==0:return 1 if j==0 else j+2 if j<=s else 2*s+1+j
  a=p-1;k=s-1;q=t-1;beta=2*t+(s-1)*q
  if j<t-2:
   b=j//2;return 2*t+b*q+a+1 if j%2==0 else 2*t+(t-1-b)*q+q-a
  if a<=k:return beta+2*a+1 if j==t-2 else beta+3*k+2-a
  r=a-k;return beta+2*r if j==t-2 else beta+4*k+3-r
 N=sum(t**g for g in range(1,n));Z=(N-t)//2+1
 def internal(h,i):
  if h==1:return Z if i==0 else N-t+1+i
  if t==2 and h==2 and i in [1,3]:i=4-i
  r=sum(t**g for g in range(h+1,n))+i;d=1+r//2
  return Z-d if r%2==0 else Z+d
 if h<n:return internal(h,i)
 q=t**(n-1);p=internal(n-1,i//t);a=p-Z if p>Z else q+1+p-Z;j=i%t
 lam=lambda b,x:N+(b-1)*q+x
 if j<t-2:
  b=j//2+1;return lam(b,a) if j%2==0 else lam(t+1-b,q+1-a)
 if j==t-2:return lam(t//2,a)
 sigma=2*a if a<=q//2 else 2*(a-q//2)-1
 return lam(t//2+1,q+1-sigma)
cases=[]
for t in [2,4,6]:
 for n in range(1,6):
  rows=[[label(t,n,h,i) for i in range(t**h)] for h in range(1,n+1)]
  flat=sum(rows,[]);m=sum(t**h for h in range(1,n+1));assert sorted(flat)==list(range(1,m+1))
  weights=[[sum(rows[0])]]
  for h in range(1,n+1):weights.append([rows[h-1][i]+(sum(rows[h][t*i:t*i+t]) if h<n else 0) for i in range(t**h)])
  assert all(weights[h][i]!=weights[h-1][i//t] for h in range(1,n+1) for i in range(t**h))
  count=len(set(sum(weights,[])));assert count==t**n+1
  case={'t':t,'n':n,'edges':m,'colors':count}
  if n==3 and t in [2,4]:case.update({'edge_rows':rows,'weight_rows':weights})
  cases.append(case)
(O/'receipts/diagnostics.json').write_text(json.dumps({'cases':cases,'diagnostic_only':True,'passed':True},indent=2)+'\n')
print('PASS: packet safety and bytes, source copies, raw line, 15 formula diagnostic cases')
