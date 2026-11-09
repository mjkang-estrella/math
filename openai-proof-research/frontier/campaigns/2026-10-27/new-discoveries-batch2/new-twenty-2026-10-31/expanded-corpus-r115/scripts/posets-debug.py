from itertools import combinations
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];out=[]
for n,s in [(6,4)]:
 S=[sum(1<<(i-1) for i in c) for c in combinations(range(1,n),s-1)];K=len(S);constraints=[]
 for l in range(1<<(n-1)):
  cuts=[i+1 for i in range(n-1) if l>>i&1];ref=odd=even=0
  for j,m in enumerate(S):
   if m&l!=m:continue
   ref|=1<<j;idx=[0]+[cuts.index(i+1)+1 for i in range(n-1) if m>>i&1]+[len(cuts)+1];q=[b-a for a,b in zip(idx,idx[1:])]
   if all(x==1 for x in q[::-2]):odd|=1<<j
   if all(x==1 for x in q[-2::-2]):even|=1<<j
  constraints.append((ref,odd,even))
 full=constraints[-1];count=0;examples=[];survive=0
 for mask in range(1,1<<K):
  if (mask&full[1]).bit_count()!=1 or (mask&full[2]).bit_count()!=1:continue
  survive+=1
  if {S[j] for j in range(K) if mask>>j&1}=={7,21,14,28}:print('DEBUG',[(l,c) for l,c in enumerate(constraints) if (mask&c[0]) and ((mask&c[1]).bit_count()!=1 or (mask&c[2]).bit_count()!=1)],flush=True)
  if all(not(mask&r) or ((mask&o).bit_count()==1 and (mask&e).bit_count()==1) for r,o,e in constraints):
   count+=1
   if len(examples)<20:examples.append([S[j] for j in range(K) if mask>>j&1])
 row=dict(n=n,s=s,compositions=K,subsets_examined=(1<<K)-1,full_stratum_filter_survivors=survive,potential_posets=count,examples_as_cut_masks=examples,limitation='generic length-s generating sets only; realizability not tested');out.append(row);print(row,flush=True)
 (D/'outputs/posets-debug.json').write_text(json.dumps(out,indent=2)+'\n')
