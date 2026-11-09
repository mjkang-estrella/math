import sys
sys.path.insert(0, sys.argv[1])
from dd344302 import dd_single
for n in range(int(sys.argv[2]), int(sys.argv[3])+1):
    vals = [dd_single(n, i) for i in range(2, n)]
    D = [vals[k+1]-vals[k] for k in range(len(vals)-1)]
    print(n, 'dd', vals)
    print(n, 'Delta', D)
