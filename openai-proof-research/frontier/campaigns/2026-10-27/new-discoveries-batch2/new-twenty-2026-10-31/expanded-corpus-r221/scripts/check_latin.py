import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for p in (D/'logs').glob('latin-solve-*.log'):
 key=p.stem.replace('latin-solve-','');parts=list(map(int,key.replace('422111','4-2-2-1-1-1').split('-')));n=sum(parts);lines=p.read_text().splitlines()
 if 's SATISFIABLE' not in lines:continue
 vals=[int(x) for l in lines if l.startswith('v ') for x in l[2:].split() if int(x)>0];grid=[[-1]*n for _ in range(n)]
 for v in vals:
  x=v-1;i=x//(n*n);j=x//n%n;k=x%n
  assert grid[i][j]==-1;grid[i][j]=k
 assert all(set(r)==set(range(n)) for r in grid)
 assert all({grid[i][j] for i in range(n)}==set(range(n)) for j in range(n))
 off=0
 for h in parts:
  assert all(off<=grid[i][j]<off+h for i in range(off,off+h) for j in range(off,off+h));off+=h
 out.append({'parts':parts,'order':n,'grid':grid,'verified':True})
(D/'outputs/latin-verified.json').write_text(json.dumps(out,indent=2));print([(o['parts'],o['verified']) for o in out])
