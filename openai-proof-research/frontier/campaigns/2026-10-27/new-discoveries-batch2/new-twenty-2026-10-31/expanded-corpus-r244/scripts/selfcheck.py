import pathlib,math,json
D=pathlib.Path(__file__).resolve().parents[1];env={'__file__':str(D/'scripts/pointed.py')};exec((D/'scripts/pointed.py').read_text().split('rows=[]')[0],env)
rows=[]
for n in range(1,8):
 got=env['check']((n,)*n);expected={((),n):math.factorial(n-1)};assert got==expected,(n,got);rows.append(['complete_pointed',n,got==expected])
env={'__file__':str(D/'scripts/hex.py')};exec((D/'scripts/hex.py').read_text().split('cur={')[0],env)
for cells,expected in [([(0,0)],[2,1]), ([(0,0),(1,0)],[3,2]), ([(0,0)]+env['dirs'],[20,32,15,2])]:
 got=env['polynomial'](cells);assert got==expected,(cells,got,expected);rows.append(['Clar_polynomial',cells,got])
print(json.dumps(rows));(D/'selfcheck.json').write_text(json.dumps(rows,indent=2))
