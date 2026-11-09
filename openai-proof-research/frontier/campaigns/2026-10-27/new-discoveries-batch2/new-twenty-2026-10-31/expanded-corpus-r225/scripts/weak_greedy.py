import pathlib,importlib.util,random,json
D=pathlib.Path(__file__).resolve().parents[1];s=importlib.util.spec_from_file_location('w',D/'scripts/weak_search.py');w=importlib.util.module_from_spec(s);s.loader.exec_module(w);old=w.subweak;rng=random.Random(43799)
def sub(a,edges,start=0,counter=None):
 if not start:
  if w.weak(a):return True
  for _ in range(80):
   b=a[:];ee=edges[:];rng.shuffle(ee)
   for x,y in ee:
    if b[x].bit_count()>2 and b[y].bit_count()>2:
     w.toggle(b,x,y)
     if w.weak(b):return True
 return old(a,edges,start,counter)
w.subweak=sub
# Independent sample: same seed, but starts at order 11 instead of order 6.
r=w.rng
for n in range(11,19):
 passed=unknown=0
 for z in range(150):
  a=[0]*n
  for i in range(n):w.toggle(a,i,(i+1)%n)
  pp=[(i,j) for i in range(n) for j in range(i+1,n) if not(a[i]>>j&1)];r.shuffle(pp)
  for x,y in pp[:r.randrange(len(pp)+1)]:
   w.toggle(a,x,y)
   if not w.weak(a):w.toggle(a,x,y)
  ok,ops=w.reduce(a)
  if ok:passed+=1
  elif ok is None:unknown+=1
  else:print(json.dumps({'FAIL':True,'n':n,'trial':z,'adjacency':a}),flush=True);raise SystemExit()
 print(json.dumps({'n':n,'trials':150,'passed':passed,'unknown':unknown}),flush=True)
