import pathlib,json,itertools,subprocess,math
D=pathlib.Path(__file__).resolve().parents[1];S='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical';out=[]
for s in range(2,6):
 for c in range(2,9):
  N=s*c;E=[(i,j) for i in range(N) for j in range(i+1,N) if i//s!=j//s];idx={e:k+1 for k,e in enumerate(E)};inc=[[idx[e] for e in E if v in e] for v in range(N)];base=[]
  for four in itertools.combinations(range(N),4):
   a,b,x,y=four
   for cyc in [[(a,b),(b,x),(x,y),(a,y)],[(a,b),(b,y),(x,y),(a,x)],[(a,x),(b,x),(b,y),(a,y)]]:
    if all(e in idx for e in cyc):base.append([-idx[e] for e in cyc])
  tests=[]
  for d in range(min(s*(c-1),int((1+math.sqrt(4*N-3))/2)),0,-1):
   clauses=base+[[-0+x for x in sub] for vs in inc for sub in itertools.combinations(vs,len(vs)-d+1)]
   p=D/'tmp/ramsey.cnf';p.write_text('p cnf %d %d\n'%(len(E),len(clauses))+''.join(' '.join(map(str,cl))+' 0\n' for cl in clauses))
   r=subprocess.run([S,'-q','-t','2',str(p)],capture_output=True,text=True)
   test={'d':d,'returncode':r.returncode};tests.append(test)
   if r.returncode==10:
    pos={int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0};assert all(any((x>0 and x in pos) or (x<0 and -x not in pos) for x in cl) for cl in clauses)
    test['edges']=[e for e in E if idx[e] in pos];break
  out.append({'s':s,'c':c,'tests':tests});(D/'outputs/ramsey.json').write_text(json.dumps(out));print(s,c,[(t['d'],t['returncode']) for t in tests],flush=True)
