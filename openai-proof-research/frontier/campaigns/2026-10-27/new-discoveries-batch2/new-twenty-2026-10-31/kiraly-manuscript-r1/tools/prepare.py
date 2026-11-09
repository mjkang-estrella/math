from pathlib import Path
import json,hashlib,shutil,re
R=Path(__file__).resolve().parents[1]; P=R.parent; A=P/'clutter-characterization-r1'; D=R/'packet'
hashof=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bind=json.loads((R/'input-bindings.json').read_text()); mismatches=[str(p) for p,h in bind.items() if hashof(P/p)!=h]; assert not mismatches,mismatches
(R/'logs/input-verification.json').write_text(json.dumps({'checked':len(bind),'mismatches':mismatches},indent=2))
for f in ['KiralyCounterexample.lean','lean-toolchain','lake-manifest.json']: shutil.copyfile(P/'candidates/kiraly-clutter-v1'/f,D/f)
for f in ['egres-tr-10-09.pdf','wb-pap-julia-2015.pdf','arxiv-1805.07576.pdf']: shutil.copyfile(A/'sources'/f,R/'sources'/f)
shutil.copyfile(P/'lane-1/sources/egres/Orientation_of_nonideal_clutters.html',R/'sources/Orientation_of_nonideal_clutters.html')
shutil.copyfile(P/'kiraly-parent-replay-r1/result.json',R/'logs/parent-replay.json')
shutil.copyfile(A/'runs/cert-n11-1.json',D/'certificate.json')
s=(D/'KiralyCounterexample.lean').read_text(); c=json.loads((D/'certificate.json').read_text()); E=c['edges']; Y=c['blocker']; T=c['tree']; assert len(E)==11 and len(Y)==36
# Compare external explanatory data against literal Lean data, including the entire tree.
for name,sets,nextname in [('XL',E,'YL'),('YL',Y,'DL')]:
 block=s.split('def '+name+' :',1)[1].split('def '+nextname+' :',1)[0]
 literal=[list(map(int,re.findall(r'\d+',x))) for x in re.findall(r'\{([0-9, ]+)\}',block)]
 assert literal==sets,(name,literal)
yidx={tuple(y):j for j,y in enumerate(Y)}
def lean_tree(t):
 if 'leaf' in t:return f'(.leaf {yidx[tuple(t["leaf"])]})'
 i=t['edge'];return f'(.node {i} '+' '.join(lean_tree(t['children'][str(v)]) for v in E[i])+')'
lit=s.split('def cert : CTree :=',1)[1].split('/-- Edge',1)[0].strip(); assert lit==lean_tree(T)
K=[[(v,[i for i,e in enumerate(E) if set(e)&set(y)=={v}]) for v in y] for y in Y]
stats={'leaves':0,'nodes':0,'depth':0,'used':set()}
def check(t,a,depth=0):
 stats['depth']=max(stats['depth'],depth)
 if 'leaf' in t:
  j=yidx[tuple(t['leaf'])];stats['used'].add(j);stats['leaves']+=1
  assert all(any(a.get(i)==v for i in ids) for v,ids in K[j]);return
 stats['nodes']+=1;i=t['edge'];assert set(t['children'])==set(map(str,E[i]))
 for v in E[i]:check(t['children'][str(v)],{**a,i:v},depth+1)
check(T,{})
for y in Y:
 assert all(set(e)&set(y) for e in E)
 for v in y:assert any(set(e)&set(y)=={v} for e in E)
# Verify the human linear elimination's equality groups from row differences.
pairs=[(1,2,8,4),(2,3,2,0),(3,4,3,1),(5,6,0,7),(6,7,5,1),(8,9,2,10),(9,10,8,5)]
for i,j,u,v in pairs:assert set(E[i])-set(E[j])=={u} and set(E[j])-set(E[i])=={v}
# After these equalities groups are a={0,2,7,10}, b={1,3,4,5,8}, c={6}, d={9}.
# e0:2a+b=1; e2:a+2b=1; e5:a+b+c=1; e8:a+b+d=1.
import sympy as sp
M=sp.Matrix([[int(v in e) for v in range(11)] for e in E]); assert M.det()!=0; assert M.inv()*sp.ones(11,1)==sp.ones(11,1)/3
# Establish type (11,3,4) for attribution without relying on an upstream classification assertion.
mate=[]
for i in range(11):
 ys=[y for y in Y if len(y)==4 and [len(set(y)&set(e)) for e in E]==[1+int(j==i) for j in range(11)]]
 assert len(ys)==1;mate.append(ys[0])
assert len({tuple(y) for y in mate})==11
stats['used']=sorted(stats['used']);stats.update({'literal_tree_matches':True,'literal_sets_match':True,'all_listed_sets_minimal_transversals':True,'incidence_determinant':int(M.det()),'lehman_mate_in_edge_order':mate,'method':'Exact Python integer/set arithmetic and SymPy rational inverse; explanatory check, Lean is proof authority'})
(R/'logs/data-check.json').write_text(json.dumps(stats,indent=2))
# Human-visible witnesses: each pair v:i means X_i intersects Y_j exactly in v.
rows=[]
for j,y in enumerate(Y):
 witnesses=', '.join(f'{v}:{ids[0]}' for v,ids in K[j]); sets=','.join(map(str,y))
 rows.append(f'{j} & $\\{{{sets}\\}}$ & \\texttt{{{witnesses}}} \\\\')
(R/'paper/witness-table.tex').write_text('\n'.join(rows)+'\n')
print(json.dumps(stats,indent=2)); print('bindings checked',len(bind))
