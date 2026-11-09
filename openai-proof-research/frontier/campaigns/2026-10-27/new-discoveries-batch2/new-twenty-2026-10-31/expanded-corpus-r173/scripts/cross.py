import pathlib,itertools,json,math
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,k,l,t in [(6,3,2,2),(6,3,3,2),(5,2,2,1),(4,2,1,1)]:
 aa=[sum(1<<x for x in a) for a in itertools.combinations(range(n),k)];bb=[sum(1<<x for x in a) for a in itertools.combinations(range(n),l)];allow=[sum(1<<j for j,b in enumerate(bb) if (a&b).bit_count()>=t) for a in aa];M=1<<len(aa);common=[0]*M;common[0]=(1<<len(bb))-1;best=0;witness=0
 for s in range(1,M):
  bit=s&-s;j=bit.bit_length()-1;common[s]=common[s^bit]&allow[j];score=s.bit_count()*common[s].bit_count()
  if score>best:best=score;witness=s
 bound=math.comb(n-t,k-t)*math.comb(n-t,l-t);r={'n':n,'k':k,'l':l,'t':t,'families_A':M,'all_B_optimized_by_common_neighborhood':True,'maximum_product':best,'bound':bound,'violation':best>bound};out.append(r);print(r,flush=True)
(D/'outputs/cross.json').write_text(json.dumps(out,indent=2))
