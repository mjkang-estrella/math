"""Tree-by-tree comparison of brute.py (Python raw rules) with the independent C++ raw-rules program."""
import networkx as nx, subprocess, brute
lines=[]; vals=[]
for n in range(2,16):
    for T in nx.nonisomorphic_trees(n):
        e=list(T.edges())
        lines.append(" ".join([str(n)]+[f"{u} {v}" for u,v in e]+["0","0"]))
        vals.append(brute.grundy_tree(n,e))
out=subprocess.run(["../raw_cpp/raw"],input="\n".join(lines)+"\n",capture_output=True,text=True,check=True).stdout.strip().split("\n")
mism=sum(1 for o,v in zip(out,vals) if int(o.split()[0])!=v)
print(len(vals),"trees compared, mismatches:",mism)
