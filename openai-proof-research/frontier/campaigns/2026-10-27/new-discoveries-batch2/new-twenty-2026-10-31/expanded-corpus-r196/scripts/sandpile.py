import pathlib,itertools,collections,json,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def top(c,n,d,itc):
 a=list(c[:n]);b=list(c[n:]);a=[x+1 for x in a];b=[x+1 for x in b];p=q=0;score=0
 for t in range(1,n+d+2):
  changed=0
  for block in ([1,0] if itc else [0,1]):
   if block==0:
    active=[i for i in range(n) if a[i]>=n+d];k=len(active)
    for i in range(n):a[i]+=k-(n+d+1)*(i in active)
    for j in range(d):b[j]+=k
    p+=k
   else:
    active=[i for i in range(d) if b[i]>=n+1];k=len(active)
    for i in active:b[i]-=n+1
    for j in range(n):a[j]+=k
    q+=k
   score+=t*k;changed+=k
  if not changed:return (tuple(a+b)==c and p==n and q==d),score
 raise RuntimeError('nontermination')
rows=[]
for n,d in [(int(sys.argv[1]),int(sys.argv[2]))]:
 C=collections.Counter();I=collections.Counter();count=rec=0;t=time.monotonic()
 for a in itertools.combinations_with_replacement(range(n+d),n):
  for b in itertools.combinations_with_replacement(range(n+1),d):
   c=a+b;count+=1;ok,x=top(c,n,d,False)
   if ok:
    ok2,y=top(c,n,d,True);assert ok2
    rec+=1;C[sum(c),x]+=1;I[sum(c),y]+=1
 delta=C-I;reverse=I-C
 r={'n':n,'d':d,'stable_sorted':count,'recurrent_sorted':rec,'equal_distributions':C==I,'positive_difference':[[list(k),v] for k,v in delta.items()],'negative_difference':[[list(k),v] for k,v in reverse.items()],'seconds':time.monotonic()-t}
 (D/f'outputs/sandpile-{n}-{d}.json').write_text(json.dumps(r,indent=2));print(r)
