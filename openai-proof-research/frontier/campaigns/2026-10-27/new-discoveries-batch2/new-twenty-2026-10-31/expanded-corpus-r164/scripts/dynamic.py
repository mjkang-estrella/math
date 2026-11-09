import pathlib,json,random,itertools,subprocess
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(164104);S='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical';out=[]
for n in [8,12,16,24,32]:
 for it in range(8):
  E=set(itertools.combinations(range(4),2));F=list(itertools.combinations(range(4),3))
  for v in range(4,n):
   f=F.pop(rng.randrange(len(F)))
   E.update((u,v) for u in f)
   F.extend(tuple(sorted((v,*pair))) for pair in itertools.combinations(f,2))
  E={e for e in E if rng.random()>.2};adj=[set() for _ in range(n)]
  for u,v in E:adj[u].add(v);adj[v].add(u)
  for r in [2,3,4,5,7,8]:
   k=r+3 if r<=2 else (r+5 if r<=7 else 3*r//2+1);var=lambda v,c:v*k+c+1;seen=lambda v,c:n*k+v*k+c+1;cl=[]
   for v in range(n):
    cl.append([var(v,c) for c in range(k)])
    cl.extend([-var(v,a),-var(v,b)] for a,b in itertools.combinations(range(k),2))
    for c in range(k):cl.append([-seen(v,c)]+[var(w,c) for w in adj[v]])
    need=min(r,len(adj[v]));cl.extend([seen(v,c) for c in sub] for sub in itertools.combinations(range(k),k-need+1))
   for u,v in E:cl.extend([-var(u,c),-var(v,c)] for c in range(k))
   p=D/'tmp/dynamic.cnf';p.write_text('p cnf %d %d\n'%(2*n*k,len(cl))+''.join(' '.join(map(str,c))+' 0\n' for c in cl))
   z=subprocess.run([S,'-q','-t','1',str(p)],capture_output=True,text=True);rec={'n':n,'iteration':it,'r':r,'k':k,'edges':sorted(E),'returncode':z.returncode}
   if z.returncode==10:
    pos={int(x) for l in z.stdout.splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0};colors=[next(c for c in range(k) if var(v,c) in pos) for v in range(n)]
    assert all(colors[u]!=colors[v] for u,v in E) and all(len({colors[w] for w in adj[v]})>=min(r,len(adj[v])) for v in range(n));rec['colors']=colors
   out.append(rec)
  print(n,it,flush=True);(D/'outputs/dynamic.json').write_text(json.dumps(out))
