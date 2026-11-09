from pathlib import Path
p=Path(__file__).resolve().parent/'eip.py'
s=p.read_text().replace('import pathlib,networkx as nx,itertools,json,sys,time,functools','import pathlib,itertools,json,sys,time,functools,gzip,hashlib')
s=s.replace('for G in nx.graph_atlas_g():\n n=len(G)', '''atlas=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i25_matching_entropy_improvement/vendor/networkx/generators/atlas.dat.gz')
(D/'outputs/atlas-provenance.json').write_text(json.dumps({'path':str(atlas),'sha256':hashlib.sha256(atlas.read_bytes()).hexdigest()}))
for block in gzip.decompress(atlas.read_bytes()).decode().split('GRAPH ')[1:]:
 lines=block.strip().splitlines();gid=int(lines[0]);n=int(lines[1].split()[1]);G={i:[] for i in range(n)}
 for line in lines[2:]:
  u,v=map(int,line.split());G[u].append(v);G[v].append(u)''')
s=s.replace('len(set(dict(G.degree()).values()))','len(set(map(len,G.values())))').replace("nx.to_graph6_bytes(G,header=False).decode().strip()","str(gid)")
p.write_text(s)
