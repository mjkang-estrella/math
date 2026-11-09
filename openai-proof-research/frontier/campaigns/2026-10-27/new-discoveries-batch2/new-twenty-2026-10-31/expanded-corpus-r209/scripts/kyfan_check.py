import sys,importlib.util
s=importlib.util.spec_from_file_location('k',sys.argv[1]);k=importlib.util.module_from_spec(s);s.loader.exec_module(k)
L=[[1,-1,0,0],[-1,2,-1,0],[0,-1,2,-1],[0,0,-1,1]]
print(k.jacobi([[float(x) for x in r] for r in L]))
print(k.kyfan([[1],[0,2],[1,3],[2]]))
print(k.kyfan([[1,2,3],[0],[0],[0]]))
import random
