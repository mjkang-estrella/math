import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];n=10;var={e:j+1 for j,e in enumerate(itertools.combinations(range(n),2))};pairs=list(itertools.combinations(range(1,5),2))
patterns={'triangle':[(1,2),(1,3),(2,3)],'paw':[(1,2),(1,3),(2,3),(3,4)],'cycle':[(1,2),(2,3),(3,4),(1,4)],'diamond':[(1,2),(1,3),(1,4),(2,3),(2,4)],'clique':pairs}
base=D/'outputs/forest10-reduced.cnf'
for name,es in patterns.items():
 with base.open('rb') as f, (D/f'outputs/forest10-{name}.cnf').open('wb') as g:
  header=f.readline().decode().split();nv,nc=map(int,header[2:4]);g.write(f'p cnf {nv} {nc+6}\n'.encode())
  for e in pairs:g.write(f'{var[e] if e in es else -var[e]} 0\n'.encode())
  while b:=f.read(1024*1024):g.write(b)
print(patterns)
