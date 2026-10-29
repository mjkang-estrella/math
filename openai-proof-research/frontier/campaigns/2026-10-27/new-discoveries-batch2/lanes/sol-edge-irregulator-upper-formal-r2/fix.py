from pathlib import Path
p=Path(__file__).parent/'formal/Upper.lean';s=p.read_text().replace('cases u; simp [graph, graphAdj, hub, node]','cases u; simp [graph, hub, node]')
a=s.index('  rcases hk with rfl');b=s.index('theorem minimum_upper',a)
s=s[:a]+'''  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
'''+''.join('  · change (Retained (graph t) (deletion t)).degree '+u+' ≠\n      (Retained (graph t) (deletion t)).degree '+v+'\n    simp only [private_degree, hub_degree]\n    norm_num <;> omega\n' for a,b in [(0,2),(1,2),(1,3),(2,4),(5,None)] for u,v in [(f'(node i {a})',f'(node i {b})' if b is not None else '(hub t)'),(f'(node i {b})' if b is not None else '(hub t)',f'(node i {a})')])+s[b:]
p.write_text(s)
