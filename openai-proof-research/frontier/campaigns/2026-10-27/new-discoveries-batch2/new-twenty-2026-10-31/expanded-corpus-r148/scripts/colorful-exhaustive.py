import pathlib,runpy,itertools,json,time
L=pathlib.Path(__file__).resolve().parents[1];betti=runpy.run_path(str(L/'scripts/colorful_core.py'))['betti'];out=[]
for m,c in [(2,2),(2,3),(2,4),(3,3),(3,4)]:
 types=list(itertools.combinations_with_replacement(range(1,1<<m),2));total=nonzero=hyp=0;k=c-m
 for sides in itertools.combinations_with_replacement(types,c):
  total+=1;b,_=betti(sides,m)
  if not b[k+1]:continue
  nonzero+=1;passes=True
  for i in range(m):
   compress=lambda x:(x&((1<<i)-1))|((x>>(i+1))<<i)
   db,_=betti([(compress(a),compress(b)) for a,b in sides],m-1)
   if any(db[:k+2]):passes=False;break
  if not passes:continue
  hyp+=1
  if not all(any(a==1<<i or b==1<<i for a,b in sides) for i in range(m)):print('COUNTEREXAMPLE',m,c,sides,b,flush=True);raise RuntimeError('candidate')
 rec={'m':m,'c':c,'k':k,'canonical_profiles':total,'nonzero_Hk':nonzero,'all_hypotheses':hyp,'counterexamples':0};out.append(rec);print(rec,flush=True);(L/'outputs/colorful-exhaustive.json').write_text(json.dumps(out,indent=2))
