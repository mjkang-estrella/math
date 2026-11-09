import sys
sys.path.insert(0, sys.argv[1])
import isogame
def path(n): 
    adj=[0]*n
    for i in range(n-1): adj[i]|=1<<(i+1); adj[i+1]|=1<<i
    return adj
def cyc(n):
    adj=path(n); adj[0]|=1<<(n-1); adj[n-1]|=1
    return adj
for n in range(3,9): print('P',n,isogame.solve(n,path(n)),'C',n,isogame.solve(n,cyc(n)))
