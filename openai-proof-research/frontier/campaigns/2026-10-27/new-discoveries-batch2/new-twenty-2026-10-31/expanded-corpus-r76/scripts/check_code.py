exec(open(__file__.replace('check_code.py','code_loops.py')).read())
F=forms[64]
t=[[2*(x^y)+(s^u^F[x*8+y]) for y,u in it.product(range(8),range(2))] for x,s in it.product(range(8),range(2))]
print('table',t)
print('assoc failures',sum(t[t[x][y]][z]!=t[x][t[y][z]] for x,y,z in it.product(range(16),repeat=3)))
print('rowlatin',all(len(set(r))==16 for r in t),'collatin',all(len(set(t[x][y] for x in range(16)))==16 for y in range(16)))
