#!/usr/bin/env python3
from pathlib import Path
import json,re
D=Path(__file__).resolve().parent
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

stats["used"]=sorted(stats["used"]);print(json.dumps(stats,indent=2))
