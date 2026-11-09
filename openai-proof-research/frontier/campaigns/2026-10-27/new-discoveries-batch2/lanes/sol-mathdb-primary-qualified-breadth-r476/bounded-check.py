from fractions import Fraction as Q
import pathlib,json
D=pathlib.Path(__file__).resolve().parent
# Finite endpoint cells suffice: every interval membership indicator is constant
# between adjacent endpoints, with endpoint inclusions checked separately.
original=[(Q(-1),Q(0),False,False),(Q(-1),Q(1),False,False),(Q(0),Q(1),True,True)]
def code(intervals):
 ends=sorted({v for a,b,_,_ in intervals for v in (a,b)});samples=[ends[0]-1,ends[-1]+1]+ends+[(a+b)/2 for a,b in zip(ends,ends[1:])]
 return sorted({tuple(i+1 for i,(a,b,lc,rc) in enumerate(intervals) if (a<x<b or x==a and lc or x==b and rc)) for x in samples})
perturbed=[(a-Q(1,3) if lc else a+Q(1,3),b+Q(1,3) if rc else b-Q(1,3),False,False) for a,b,lc,rc in original]
a=code(original);b=code(perturbed)
assert a==[(),(1,2),(2,3),(3,)] and (2,) in b and (2,) not in a
r={'mathdb_id':337624,'status':'PASS bounded sanity check ONLY; zero discovery credit','original_intervals':['(-1,0)','(-1,1)','[0,1]'],'original_code':a,'epsilon':'1','source_proposed_perturbation_code':b,'new_word':[2],'certificate_scope':'Exact finite endpoint-cell check, no arbitrary-real sampling inference. Source perturbation is not universally code preserving for arbitrary intervals.','objection':'Code is not open convex in any dimension: U2 would be a union of disjoint nonempty relatively open U1-intersection and U3-intersection, contradicting connectedness. Source Definition 5 only defines minimal open dimension for open convex codes. This is a domain/standard connectedness obstruction, not a qualified new full-scope result.','not_claimed':['no refutation of the source restricted open-convex interpretation','no novelty','no accepted credit','no proof of conjecture']}
(D/'bounded-check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
