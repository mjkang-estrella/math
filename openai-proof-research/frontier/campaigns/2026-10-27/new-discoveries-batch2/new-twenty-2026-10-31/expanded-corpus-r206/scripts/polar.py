import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def form(a,b):return (((a&3)&(b>>2)).bit_count()+((a>>2)&(b&3)).bit_count())%2
ls=sorted({tuple(sorted((a,b,a^b))) for a in range(1,16) for b in range(a+1,16) if not form(a,b)})
best=[];size=0;valid=0
for mask in range(1<<len(ls)):
 if mask.bit_count()<size:continue
 inds=[i for i in range(len(ls)) if mask>>i&1]
 if any(not set(ls[i])&set(ls[j]) for i,j in itertools.combinations(inds,2)):continue
 if len(inds)>size:size=len(inds);best=[]
 best.append(inds)
stars={tuple(i for i,l in enumerate(ls) if p in l) for p in range(1,16)}
r={'space':'W(3,2)','rank_d':2,'t':1,'generators':len(ls),'subsets_checked':1<<len(ls),'maximum_EKR':size,'maximizers':len(best),'all_maximizers_are_stars':all(tuple(v) in stars for v in best)}
print(json.dumps(r));(D/'outputs/polar-W3-2.json').write_text(json.dumps(r,indent=2))
