import sys, subprocess, time
from collections import Counter
n=int(sys.argv[1])
t=time.time()
inp=subprocess.run([sys.executable,"gen_trees.py",str(n)],capture_output=True,text=True).stdout.strip().split("\n")
out=subprocess.run(["./raw"],input="\n".join(inp)+"\n",capture_output=True,text=True).stdout.strip().split("\n")
assert len(inp)==len(out)
dist=Counter(); cex=[]; big=[]
for L,O in zip(inp,out):
    g,m=map(int,O.split()[:2]); dist[g]+=1
    if (g==0)!=(m%2==0): cex.append((g,m,L))
    if g>=2: big.append((g,m,L))
print("n=",n,"trees",len(out),"dist",dict(sorted(dist.items())),"parity-conj counterexamples",len(cex),"g!=m%2:",sum(1 for L,O in zip(inp,out) if int(O.split()[0])!=int(O.split()[1])%2),"time %.0fs"%(time.time()-t),flush=True)
if len(cex)<=10:
    for c in cex: print("  CEX",c)
for b in big[:10]: print("  BIG",b)
