import re,json,sys,itertools
src=open(sys.argv[1]).read()
m=re.search(r'def tris[^\[]*\[(.*?)\]\n',src,re.S)
tups=[tuple(map(int,t.split(','))) for t in re.findall(r'\(([\d, ]+)\)',m.group(1))]
mine=json.load(open('checks/v3-independent.json'))
L=[{0,2,3},{2,4,5},{3,5,8},{2,7,8},{1,3,6},{0,6,8},{0,1,4},{4,6,7},{1,5,7}]
ok=[]
for a,b,c,i,j,k in tups:
    ok.append(a in L[i] and b in L[i] and c not in L[i] and b in L[j] and c in L[j] and a not in L[j] and a in L[k] and c in L[k] and b not in L[k])
# Lean M table vs list
Mlean=re.findall(r'\| (\d|_) => (p\.val == \d(?: \|\| p\.val == \d)*)',src)
lines=[sorted(int(x) for x in re.findall(r'== (\d)',rhs)) for _,rhs in Mlean]
print(json.dumps({'n_lean_tris':len(tups),'distinct_line_triples':len({frozenset(t[3:]) for t in tups}),'all_valid':all(ok),'lean_M_lines':lines,'M_matches_stated':lines==[sorted(l) for l in L]}))
