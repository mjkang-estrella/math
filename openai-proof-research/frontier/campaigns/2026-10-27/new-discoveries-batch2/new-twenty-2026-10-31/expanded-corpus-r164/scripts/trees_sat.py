import pathlib,json,itertools,subprocess
D=pathlib.Path(__file__).resolve().parents[1];S='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical';r=json.loads((D/'outputs/trees-16.json').read_text());out=[];n=16;B=31;var=lambda obj,x:obj*B+x
for row in r:
 if row['status']=='witness':continue
 E=row['edges'];cl=[]
 for a in range(B):
  cl.append([var(a,x) for x in range(1,B+1)])
  for x,y in itertools.combinations(range(1,B+1),2):cl.append([-var(a,x),-var(a,y)])
 for x in range(1,B+1):
  for a,b in itertools.combinations(range(B),2):cl.append([-var(a,x),-var(b,x)])
 for e,(u,v) in enumerate(E):
  for x in range(1,B+1):
   for y in range(1,B+1):
    if x!=y:cl.append([-var(u,x),-var(v,y),var(n+e,x^y)])
 u,v=E[0];cl.extend([[var(u,1)],[var(v,2)]])
 p=D/'tmp/tree.cnf';p.write_text('p cnf %d %d\n'%(B*B,len(cl))+''.join(' '.join(map(str,c))+' 0\n' for c in cl))
 z=subprocess.run([S,'-q','-t','5',str(p)],capture_output=True,text=True);rec={'canonical':row['canonical'],'returncode':z.returncode,'edges':E}
 if z.returncode==10:
  pos={int(x) for l in z.stdout.splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0};labels=[next(x for x in range(1,B+1) if var(v,x) in pos) for v in range(n)]
  assert sorted(labels+[labels[u]^labels[v] for u,v in E])==list(range(1,B+1));rec['labels']=labels
 out.append(rec);(D/'outputs/trees-sat.json').write_text(json.dumps(out));print(len(out),z.returncode,flush=True)
