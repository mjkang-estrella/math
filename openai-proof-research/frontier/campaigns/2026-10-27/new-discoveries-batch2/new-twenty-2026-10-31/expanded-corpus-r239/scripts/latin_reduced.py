import pathlib,random,time,json
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(239);start=time.monotonic();rows=[]
patterns={"a":["10"]*3,"b":["10","11"],"c":["10","101"],"d":["10","1010"],"f":["1110"],"g":["10101"],"h":["101010"]}
cases=[(family,k) for k in range(1,7) for family in patterns]
for family,k in cases:
 words=patterns[family]+["00"]*(k+(family in "bcfg")); n=sum(map(len,words))
 if n<9:continue
 marks=[];perm=[];offset=0
 for word in words:
  marks.extend(offset+i for i,c in enumerate(word) if c=="1");perm.extend(offset+(i+1)%len(word) for i in range(len(word)));offset+=len(word)
 order=marks+[i for i in range(n) if i not in marks];inv={v:i for i,v in enumerate(order)};second=[inv[perm[v]] for v in order]
 complete=unknown=0;nodes=0; generated=0
 for trial in range(150):
  if time.monotonic()-start>105:break
  full=(1<<n)-1;p=[[-1]*n for _ in range(n)];p[0]=list(range(n));s=list(range(n))
  s=second[:]
  p[1]=s[:];rm=[0]*n;cm=[0]*n
  for r in range(2):
   for c in range(n):rm[r]|=1<<p[r][c];cm[c]|=1<<p[r][c]
  slots=[(r,c) for r in range(2,n) for c in range(3)]
  def fill_columns(j):
   if j==len(slots):return True
   r,c=slots[j];opts=[x for x in range(n) if not (rm[r]|cm[c])>>x&1];rng.shuffle(opts)
   for x in opts:
    p[r][c]=x;rm[r]|=1<<x;cm[c]|=1<<x
    if fill_columns(j+1):return True
    rm[r]^=1<<x;cm[c]^=1<<x;p[r][c]=-1
   return False
  if not fill_columns(0):continue
  generated+=1;initial=[r[:] for r in p];cnt=[0];deadline=time.monotonic()+.35
  def solve():
   cnt[0]+=1
   if cnt[0]%128==0 and time.monotonic()>deadline:raise TimeoutError
   best=None;bm=0
   for r in range(2,n):
    for c in range(3,n):
     if p[r][c]>=0:continue
     m=full&~(rm[r]|cm[c]);l=m.bit_count()
     if l==0:return False
     if best is None or l<bm.bit_count():best=(r,c);bm=m
   if best is None:return True
   r,c=best
   while bm:
    bit=bm&-bm;bm^=bit;x=bit.bit_length()-1;p[r][c]=x;rm[r]|=bit;cm[c]|=bit
    if solve():return True
    rm[r]^=bit;cm[c]^=bit;p[r][c]=-1
   return False
  try:
   ok=solve()
   if not ok:
    (D/'latin-reduced-obstruction-diagnostic.json').write_text(json.dumps({'n':n,'partial':initial}));print('OBSTRUCTION',n,initial,flush=True);raise SystemExit
   assert all(sorted(r)==list(range(n)) for r in p)
   assert all(sorted(p[r][c] for r in range(n))==list(range(n)) for c in range(n));complete+=1
  except TimeoutError:unknown+=1
  nodes+=cnt[0]
 rows.append({'family':family,'k':k,'n':n,'generated':generated,'completed_and_checked':complete,'indeterminate_timeouts':unknown,'nodes':nodes});print(rows[-1],flush=True)
(D/'latin-reduced-search.json').write_text(json.dumps({'seed':239,'rows':rows,'seconds':time.monotonic()-start,'claim':'Biased random samples, not exhaustive; timeouts indeterminate.'},indent=2)+'\n')
