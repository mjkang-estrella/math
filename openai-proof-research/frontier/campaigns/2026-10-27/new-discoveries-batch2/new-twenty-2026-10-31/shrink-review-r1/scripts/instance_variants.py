"""shrink-review-r1: terminal outcomes of the 346320 instance under V1/V2/V3 (variant_search.St)."""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from variant_search import St
Y = [1, 2, 2, 2, 2, 2]                       # 2*y
X = {(0, 4): 1, (0, 5): 1, (2, 3): 1, (2, 5): 1, (3, 4): 1, (1, 2): 2, (1, 3): 2, (4, 5): 2}   # 2*x
st = St(6, Y, X)
out = {}
for var, depots in [("V1", [None]), ("V2", [None]), ("V3", [1, 2, 3, 4, 5])]:
    for d in depots:
        T = st.explore(var, d)
        out["%s depot=%s" % (var, d)] = sorted([sorted(sorted(b for b in range(6) if B >> b & 1) for B in P) for P in T])
print(json.dumps(out, indent=1))
