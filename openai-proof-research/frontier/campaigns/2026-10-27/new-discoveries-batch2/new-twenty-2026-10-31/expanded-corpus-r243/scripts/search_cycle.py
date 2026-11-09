import itertools,json,time
start=time.monotonic()
for s,t in [(3,8),(3,9),(3,10),(4,10),(4,11),(5,12)]:
 sets=[sum(1<<i for i in c) for c in itertools.combinations(range(t),s) if all((i+1)%t not in c for i in c)]
 full=(1<<t)-1
 def rainbow(fam,used=0):
  if not fam:return True
  block=used|((used<<1)&full)|(used>>1)|((used&1)<<(t-1))|(used>>(t-1))
  opts=[x&~block for x in fam];i=min(range(len(opts)),key=lambda i:opts[i].bit_count());avail=opts[i]
  rest=fam[:i]+fam[i+1:]
  while avail:
   b=avail&-avail;avail-=b
   if rainbow(rest,used|b):return True
  return False
 cnt=0
 for fam in itertools.combinations_with_replacement(sets,s):
  cnt+=1
  if not rainbow(fam):print(json.dumps({'counterexample':fam,'s':s,'t':t}),flush=True);raise SystemExit(2)
 print(json.dumps({'s':s,'t':t,'independent_sets':len(sets),'multisets_tested':cnt,'counterexamples':0,'elapsed':time.monotonic()-start}),flush=True)
