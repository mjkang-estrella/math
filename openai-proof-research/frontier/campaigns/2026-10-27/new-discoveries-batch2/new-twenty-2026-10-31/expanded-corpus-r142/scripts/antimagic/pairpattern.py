import sys
def sol(q):
  k=q//2; target={2*q+1+d for d in range(1,k+1)}|{2*q+1-d for d in range(1,k+1)}
  used=[False]*(2*q+1); res=[]
  def dfs(rem):
    i=next((x for x in range(1,2*q+1) if not used[x]),None)
    if i is None: return True
    used[i]=True
    for j in range(i+1,2*q+1):   # smallest partner first
      if not used[j] and (i+j) in rem:
        used[j]=True; res.append((i,j,i+j-2*q-1))
        if dfs(rem-{i+j}): return True
        res.pop(); used[j]=False
    used[i]=False; return False
  dfs(frozenset(target)); return res
for q in range(4,int(sys.argv[1])+1,2): print(q, sol(q))
