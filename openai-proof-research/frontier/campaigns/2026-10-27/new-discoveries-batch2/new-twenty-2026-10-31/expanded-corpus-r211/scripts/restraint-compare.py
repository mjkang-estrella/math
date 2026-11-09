import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];P=D/'scripts/restraints.py';ns={'__name__':'library','__file__':str(P)};exec(compile(P.read_text().split('out=[]\nfor n in range(5')[0],str(P),'exec'),ns)
canon=ns['canon'];poly=ns['polynomial'];out=[]
for row in json.loads((D/'outputs/restraints.json').read_text()):
 n=row['n']
 if n%4!=3:continue # all ranges in printed source unambiguous
 r=[None]*n
 for i in range(1,(n-1)//2+1,2):r[i-1]=0
 for i in list(range(2,(n-3)//2+1,2))+list(range((n+3)//2,n+1,2)):r[i-1]=1
 for i in range((n+1)//2,n,2):r[i-1]=2
 p=poly(r);best=row['polynomial_descending'];delta=[a-b for a,b in zip(best,reversed(p))];first=next(((n-j,d) for j,d in enumerate(delta) if d),None)
 ans={'n':n,'source_rstar':r,'canonical':canon(r),'source_polynomial_descending':list(reversed(p)),'first_improvement_degree_and_coefficient':first};out.append(ans);print(ans)
(D/'outputs/restraint-compare.json').write_text(json.dumps(out,indent=2)+'\n')
