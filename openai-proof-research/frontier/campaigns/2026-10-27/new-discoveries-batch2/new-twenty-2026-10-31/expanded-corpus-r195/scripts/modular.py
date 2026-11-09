import pathlib,json,itertools,math
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for q,n,r in [(4,3,1),(5,5,2),(7,8,3),(8,10,4)]:
 F=[sum(1<<i for i in c) for c in itertools.combinations(range(n),r)];L=set(range(r));k=2;t=1
 ok=all(a.bit_count()%q not in L for a in F) and all((a&b).bit_count()%q in L for a,b in itertools.combinations(F,2))
 bound=math.comb(n,q-1) if n>=q-1 else 0
 out.append({'q':q,'n':n,'r':r,'k':k,'t':t,'L':sorted(L),'family':'all r-subsets','size':len(F),'bound':bound,'hypotheses':ok,'violates':len(F)>bound,'credit':'zero: small-ambient-dimension formulation failure'})
print(out);(D/'outputs/modular.json').write_text(json.dumps(out,indent=2))
