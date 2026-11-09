import pathlib,json,random,sys,hashlib,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(164342);out=[]
def euler(n,removed,start):
 mask=(1<<(n-1))-1;N=1<<(n-1);adj=[]
 for v in range(N):
  a=[b for b in [0,1] if ((v<<1)|b) not in removed];rng.shuffle(a);adj.append(a)
 stack=[(start,-1)];bits=[]
 while stack:
  v,b=stack[-1]
  if adj[v]:
   x=adj[v].pop();stack.append((((v<<1)|x)&mask,x))
  else:
   stack.pop()
   if b>=0:bits.append(b)
 if len(bits)!=(1<<n)-len(removed):return None
 bits.reverse();return bits
for n in [14,15,16]:
 ks=sorted(set([n+1,n+2,2*n,3*n]+[1<<j for j in range(6,n)]))
 for k in ks:
  found=None
  for attempt in range(40):
   # Generate a random Euler cycle; initial (n-1)-block fixed at 0 by choice.
   initial=rng.randrange(1<<(n-1));b=euler(n,set(),initial);pre=[int(x) for x in format(initial,'0%db'%(n-1))]+b[:k-n] # exactly k-1 symbols
   if len(pre)!=k-1:raise Exception()
   word=pre+[-1]+pre[:n-1]+[1-pre[n-1]]
   removed=set();ok=True
   for j in range(len(word)-n+1):
    w=word[j:j+n];vals=[0]
    for x in w:vals=[(a<<1)|v for a in vals for v in ([0,1] if x<0 else [x])]
    if any(v in removed for v in vals):ok=False;break
    removed.update(vals)
   if not ok:continue
   start=0
   for x in word[-(n-1):]:start=(start<<1)|x
   tail=euler(n,removed,start)
   if tail is None:continue
   w=word+tail;seen=[0]*(1<<n)
   for j in range(len(w)-n+1):
    vals=[0]
    for x in w[j:j+n]:vals=[(a<<1)|v for a in vals for v in ([0,1] if x<0 else [x])]
    for v in vals:seen[v]+=1
   if set(seen)!={1}:continue # degree obstruction can make Hierholzer sequence invalid
   text=''.join('?' if x<0 else str(x) for x in w)+'\n';p=D/'outputs'/('upword-%d-%d.txt'%(n,k));p.write_text(text);found={'file':str(p),'sha256':hashlib.sha256(text.encode()).hexdigest(),'length':len(w)};break
  out.append({'n':n,'k':k,'attempts':attempt+1,'witness':found});(D/'outputs/upwords-random-start.json').write_text(json.dumps(out));print(n,k,attempt+1,bool(found),flush=True)
