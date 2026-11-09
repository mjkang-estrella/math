import itertools,pathlib,json
mul=lambda a,b:tuple(a[b[i]] for i in range(len(a)))
inv=lambda a:tuple(a.index(i) for i in range(len(a)))
B=[tuple(int(c)-1 for c in s) for s in ['51234','52143','53412','54321','41235','42153','43512','45321']]
# Full-of-flips from Eq (7.2), author-hosted 2010 primary body, p.973.
pairs=[]
for i,a in enumerate(B):
 for j,b in enumerate(B):
  if i<j:
   witnesses=[(k,l) for k in range(5) for l in range(k+1,5) if a[k]==b[l] and a[l]==b[k]]
   assert witnesses;pairs.append({'i':i,'j':j,'flips':witnesses})
C={mul(a,inv(B[0])) for a in B};E=tuple(range(5));assert E in C
bad=next((a,b,mul(a,b)) for a in C for b in C if mul(a,b) not in C)
r={'citation':'Furedi, Kantor, Monti, Sinaimeri (2010), Section 7, Eqs (7.1)-(7.2), pp.972-973','source_family_one_based':[''.join(str(x+1) for x in a) for a in B],'normalized_family_zero_based':sorted(C),'cardinality':len(C),'identity_present':E in C,'nonclosure':bad,'all_28_flip_checks':pairs,'implication':'8 reversing permutations are even-cycle-intersecting. Normalized family is not a subgroup. Under the proposed classification its cardinality equals a Sylow subgroup and it must be maximum, contradiction. Refutation is an elementary corollary of the published explicit construction.'}
pathlib.Path('outputs/prior-obstruction.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
