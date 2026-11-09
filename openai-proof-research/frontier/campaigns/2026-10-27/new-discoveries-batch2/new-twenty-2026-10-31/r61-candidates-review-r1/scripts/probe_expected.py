import sys;sys.path.insert(0,sys.argv[1])
from cat_verify import build,stars_dp
adj=build((1,4,6,5,0,6))
for r in (3,4,5): print(r,stars_dp(adj,r)[27])
