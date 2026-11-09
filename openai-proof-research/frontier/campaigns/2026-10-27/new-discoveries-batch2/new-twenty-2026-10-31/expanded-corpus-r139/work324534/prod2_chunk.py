import sys, json, pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent)); from prod2 import solve
n,lo,hi=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); fails=[]; c=0
for idx,l in enumerate(open(f'graphs/g{n}.txt')):
    if idx<lo or idx>=hi or not l.strip(): continue
    g=list(map(int,l.split())); c+=1
    if not solve(g): fails.append(g)
print(json.dumps({'n':n,'range':[lo,hi],'checked':c,'fails':fails[:10]}))
