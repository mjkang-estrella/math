import pathlib,json,itertools
L=pathlib.Path(__file__).resolve().parent
def step(q,s,c):
 if s is None:return None
 suffix,age=s;suffix=(suffix+c)[-len(q):]
 if suffix==q:return suffix,0
 age+=1
 return None if age>=len(q) else (suffix,age)
def cover(u,v,q):
 s=('',0)
 for c in u:
  s=step(q,s,c)
  if s is None:return False
 seen=set()
 while s not in seen:
  seen.add(s)
  for c in v:
   s=step(q,s,c)
   if s is None:return False
 return True
def absent(u,v):
 # A prefix longer than preperiod+period distinguishes any non-pure-periodic lasso.
 n=len(u)+len(v);prefix=(u+v*(n+1))[:n]
 for j in range(len(v)):
  if prefix==(v*(n+2))[j:j+n]:return None
 return prefix
def words(n,A='ab'):return [''.join(w) for k in range(1,n+1) for w in itertools.product(A,repeat=k)]
failed=L/'lasso-checks.json'
if failed.exists() and not (L/'FAILED-prefix-absence-only.json').exists():
 (L/'FAILED-prefix-absence-only.json').write_bytes(failed.read_bytes())
out=[]; old=0
for A,B in itertools.product(words(3),repeat=2):
 f={'a':A,'b':B};wit=None
 for u,v in itertools.product(words(3),repeat=2):
  p=absent(u,v)
  if p is None:continue
  # Absence of ONE long prefix is insufficient: exclude every shorter cover.
  if any(cover(u,v,p[:m]) for m in range(1,len(p))):continue
  U=''.join(f[c] for c in u);V=''.join(f[c] for c in v)
  for m in range(1,13):
   q=(U+V*20)[:m]
   if cover(U,V,q):wit={'a':A,'b':B,'u':u,'v':v,'absent_prefix':p,'q':q};break
  if wit:break
 if wit:out.append(wit)
 # both oriented unique-letter witnesses, unlike inherited one orientation only
 for u,v in [('a','b'),('b','a')]:
  if any(cover(f[u],f[v],(f[u]+f[v]*20)[:m]) for m in range(1,13)):
   old+=1;break
assert absent('ab','ab') is None
assert absent('aba','ba') is None
assert absent('aab','ab') is not None
assert cover('aba'+'b','aba','aba')
assert cover('ab','aba','aba')  # non-pure-periodic, yet quasiperiodic
result={'tested':196,'u_v_max_length':3,'q_max_length':12,'certified':len(out),'either_oriented_unique_letter':old,'witnesses':out,'scope':'Positive certificates only; no universal or negative conclusion.'}
(L/'lasso-checks.json').write_text(json.dumps(result,indent=2));print({k:v for k,v in result.items() if k!='witnesses'})
