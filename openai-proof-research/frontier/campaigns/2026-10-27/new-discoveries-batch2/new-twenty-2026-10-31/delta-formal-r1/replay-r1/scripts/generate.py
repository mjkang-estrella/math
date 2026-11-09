import json,pathlib
P=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((P.parent/'expanded-corpus-r153/outputs/pure-dag.json').read_text())
a=r['nodes'][r['root']]['graph']
def reduce(g,x):
 ns=[i for i in range(len(g)) if g[x][i]]
 assert len(ns)==3 and all(g[x][i]==2 for i in ns)
 keep=[i for i in range(len(g)) if i!=x]
 return [[g[i][j]+int(i!=j and i in ns and j in ns) for j in keep] for i in keep],ns
def expand(g,tri):
 n=len(g);h=[row+[0] for row in g]+[[0]*(n+1)]
 for i in tri:
  for j in tri:
   if i!=j:
    assert h[i][j]>0
    h[i][j]-=1
  h[i][n]=h[n][i]=2
 return h
out=['import Literal','import Delta153','namespace Concrete','open Literal', 'set_option maxRecDepth 4096', 'set_option maxHeartbeats 4000000']
graphs=[a]; moves=[]
for x in [0,0,3,4,6,7,11]:
 h,ns=reduce(graphs[-1],x);moves.append(('down',x,ns));graphs.append(h)
for kind,args in [('up',[1,6,8]),('down',6),('up',[4,7,10]),('up',[3,7,10]),('down',10),('down',7),('down',9)]:
 if kind=='up':
  h=expand(graphs[-1],args);moves.append(('up',len(h)-1,args))
 else:h,ns=reduce(graphs[-1],args);moves.append(('down',args,ns))
 graphs.append(h)
for i,g in enumerate(graphs):
 out += [f'def rows{i} : Delta153.Graph := {g}',f'def g{i} : Graph where',f'  order := {len(g)}',f'  edge i j := Delta153.edge rows{i} i.val j.val','  symm := by decide','  loopless := by decide']
for i,(kind,x,ns) in enumerate(moves):
 lo,hi=(i+1,i) if kind=='down' else (i,i+1)
 n=len(graphs[hi]);m=n-1
 keep=f'(fun i => (⟨if i.val < {x} then i.val else i.val + 1, by split <;> omega⟩ : Fin {n}))'
 out += [f'theorem move{i} : YYDelta g{hi} g{lo} := by',f'  unfold YYDelta',f'  dsimp only [g{hi}, g{lo}]',f'  refine ⟨{x}, {ns[0]}, {ns[1]}, {ns[2]}, {keep}, ?_⟩','  decide']
out += ['theorem original_doubled_cubic : DoubledCubic g0 := by unfold DoubledCubic; decide','theorem pure_path : Pure g0 g7 := by']
for i in range(7):out += [f'  apply Pure.step move{i}']
out += ['  exact Pure.refl _','theorem seven_move_witness : Equivalent g7 g14 := by']
for i,(kind,*_) in enumerate(moves[7:],7):out += [f'  apply Equivalent.step (Or.{"inl" if kind=="down" else "inr"} move{i})']
out += ['  exact Equivalent.refl _','theorem order_drop : g14.order < g7.order := by decide','theorem chosen_order : g7.order = 11 := rfl','theorem nonminimal : ¬ Minimal g7 := smaller_equivalent_not_minimal seven_move_witness order_drop','#print axioms pure_path','#print axioms seven_move_witness','#print axioms nonminimal','end Concrete']
(P/'lean/Concrete.lean').write_text('\n'.join(out)+'\n')
print('Generated',len(graphs),'literal symmetric loopless graphs and',len(moves),'move obligations')
text='\n'.join(out)+'\n'
start=text.index('theorem move0')
end=text.index('theorem original_doubled_cubic')
(P/'lean/Nodes.lean').write_text(text[:start]+'end Concrete\n')
for i in range(14):
 a=text.index(f'theorem move{i} :'); b=text.index(f'theorem move{i+1} :') if i<13 else end
 (P/f'lean/Move{i:02}.lean').write_text(f'import Nodes\nnamespace Concrete\nopen Literal\nset_option maxRecDepth 4096\nset_option maxHeartbeats 4000000\n'+text[a:b]+'end Concrete\n')
(P/'lean/Concrete.lean').write_text('\n'.join(f'import Move{i:02}' for i in range(14))+'\nnamespace Concrete\nopen Literal\n'+text[end:])
