from fractions import Fraction as F
import json,pathlib,itertools
P=pathlib.Path(__file__).parent
profiles={'constant':[1]*7,'linear':list(range(1,8)),'quadratic':[(k+1)**2 for k in range(7)],'exponential':[2**k for k in range(7)],'step1':[1]+[2]*6,'step2':[1]*2+[2]*5,'step2ten':[1]*2+[10]*5,'step3ten':[1]*3+[10]*4}
def stats(w,n):
 out=[F(0),F(0)];count=0
 def walk(deg,dep,p):
  nonlocal count
  if len(dep)==n:out[0]+=p*dep[-1];out[1]+=p*max(dep);count+=1;return
  den=sum(w[x] for x in deg)
  for i in range(len(dep)):
   d=deg.copy();d[i]+=1;walk(d+[0],dep+[dep[i]+1],p*F(w[deg[i]],den))
 walk([0],[0],F(1));return [str(x) for x in out],count
vals={name:{n:stats(w,n) for n in range(2,8)} for name,w in profiles.items()};pairs=[]
for f,g in itertools.permutations(profiles,2):
 if all(profiles[f][k+1]*profiles[g][k]>=profiles[g][k+1]*profiles[f][k] for k in range(6)):
  violations=[n for n in range(2,8) if any(F(vals[f][n][0][i])>F(vals[g][n][0][i]) for i in [0,1])];pairs.append({'f':f,'g':g,'violating_n':violations})
obj={'id':373157,'executed':True,'method':'exact rational enumeration of every recursive parent vector; source out-degree convention','n_range':[2,7],'profiles_values_k0_to6':profiles,'expectations_depth_height_and_tree_counts':vals,'GRD_pairs_on_relevant_degrees':pairs,'limit':'Only finite n and eight profiles; no full-scope coupling or proof; GRD can be extended by freezing each ratio after degree 6.'}
(P/'bounded-checks.json').write_text(json.dumps(obj,indent=2)+'\n');print('pairs',len(pairs),'violations',[p for p in pairs if p['violating_n']])
