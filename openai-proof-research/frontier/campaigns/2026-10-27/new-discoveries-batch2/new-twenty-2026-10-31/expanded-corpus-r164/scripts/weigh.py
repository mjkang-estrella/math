import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];out=[]
# All augmented comparisons using w != y and x != z, w,y,x,z within same size block.
for f in range(2,9):
 for r in range(1,f):
  for k in range(4,8):
   sizes=[(k-2,1,2)]*r+[(k-3,2,1)]*(f-r)
   # all original balance outcomes imply A_i+B_i=a, B_i+C_i=b.
   # extra swapped comparisons force B constant within each block of size >=2;
   # singleton blocks are constant vacuously. Thus exhaust block B-values.
   bad=[];admissible=[]
   for a,b,bl,bs in itertools.product(range(k),range(4),range(2),range(3)):
    vals=[(a-bl,bl,b-bl)]*r+[(a-bs,bs,b-bs)]*(f-r)
    if not all(all(0<=v<=cap for v,cap in zip(x,y)) for x,y in zip(vals,sizes)):continue
    d=sum(map(sum,vals));admissible.append(d)
    t=f*k+r
    if 0<d<t and d!=f and (d<f or all(d not in (q*f,q*f-r,q*f+r) for q in range(1,k+2))):bad.append({'d':d,'counts':vals,'a':a,'b':b})
   out.append({'f':f,'r':r,'k':k,'admissible_d':sorted(set(admissible)),'augmented_strategy_failures':bad})
(D/'outputs/weigh.json').write_text(json.dumps(out));print('parameter triples',len(out),'with diagnostic failure',sum(bool(x['augmented_strategy_failures']) for x in out));print(next(x for x in out if x['augmented_strategy_failures']))
