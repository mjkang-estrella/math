import networkx as nx,pathlib,random
D=pathlib.Path(__file__).resolve().parents[1]
for n in [6,7]:
 lines=[]
 for i,g in enumerate(nx.graph_atlas_g()):
  if len(g)!=n:continue
  e=list(g.edges());lines.append(f'{i} {n} {len(e)} '+' '.join(f'{a} {b}' for a,b in e))
 (D/f'outputs/gp-atlas-{n}.in').write_text('\n'.join(lines)+'\n')
