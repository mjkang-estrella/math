import itertools,pathlib,json,collections,math
L=pathlib.Path(__file__).resolve().parents[1]
def parity(p):return (-1)**sum(p[i]>p[j]for i in range(len(p))for j in range(i+1,len(p)))
def canon(rows,k,l):
 # Sort columns after each row permutation; this covers independent row and column actions.
 return min(tuple(sorted(sum(((rows[p[i]]>>j)&1)<<i for i in range(k))for j in range(l)))for p in itertools.permutations(range(k)))
def stabilizer_even(cols,k,l):
 # Identical columns may be transposed while fixing the rows.
 if any(c>1 and k-col.bit_count()%2==1 for col,c in []):pass
 groups=collections.defaultdict(list)
 for j,col in enumerate(cols):groups[col].append(j)
 for col,js in groups.items():
  if len(js)>1 and (k-col.bit_count())%2:return False,None
 # cols encode holes, so the edge set is its complement.
 edges=[(i,j)for i in range(k)for j in range(l)if not(cols[j]>>i&1)];ix={e:i for i,e in enumerate(edges)};aut=0
 for p in itertools.permutations(range(k)):
  transformed=[sum(((col>>i)&1)<<p[i]for i in range(k))for col in cols]
  if sorted(transformed)!=list(cols):continue
  used=collections.Counter();q=[]
  for c in transformed:q.append(groups[c][used[c]]);used[c]+=1
  induced=[ix[p[i],q[j]]for i,j in edges];aut+=1
  if parity(induced)<0:return False,{'row_permutation':p,'column_permutation':q}
 return True,aut
out={}
for k,l in [(5,5),(4,6)]:
 holes=k*l-20;seen=set();reps=[];tested=0
 for missing in itertools.combinations(range(k*l),holes):
  rows=[0]*k
  for x in missing:rows[x//l]|=1<<(x%l)
  if any(r==(1<<l)-1 for r in rows):continue
  if any(all(r>>j&1 for r in rows)for j in range(l)):continue
  c=canon(rows,k,l);tested+=1
  if c in seen:continue
  seen.add(c);even,detail=stabilizer_even(c,k,l);reps.append({'holes_by_columns':c,'all_stabilizers_even':even,'detail':detail})
 good=sum(r['all_stabilizers_even']for r in reps);out[f'{k}x{l}']={'matrices':tested,'orbits':len(reps),'sign_multiplicity':good,'representatives':reps};print(k,l,len(reps),good,flush=True);(L/'outputs/sign-orbits.json').write_text(json.dumps(out,indent=2))
print('DIFFERENCE',out['5x5']['sign_multiplicity']-out['4x6']['sign_multiplicity'])
