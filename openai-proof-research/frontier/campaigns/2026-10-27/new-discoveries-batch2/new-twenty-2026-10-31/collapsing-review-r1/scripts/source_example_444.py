"""Sanity: rank of the starred cells of the source's non-collapsible 4x4x4 facet (Example, sec:three).
Reading: rows = i, the four blocks = k, columns in a block = j; '*' cells are the extreme rays in the facet.
Facet requires rank 36 = dim P^{4,4,4} - 1. Usage: python3 -I source_example_444.py"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_facet import rank, column
rows = ["000*|*00*|**0*|****", "00**|*0**|****|00*0", "0***|****|0*00|0**0", "****|*000|**00|***0"]
star = []
for i, row in enumerate(rows):
    for k, blk in enumerate(row.split("|")):
        for j, ch in enumerate(blk):
            if ch == "*":
                star.append((i, j, k))
print("starred", len(star), "rank", rank([column(4, 4, 4, *c) for c in star]))
# same cells read with blocks = j and in-block columns = k
star2 = [(i, k, j) for (i, j, k) in star]
print("alt reading rank", rank([column(4, 4, 4, *c) for c in star2]))
def pats(axis):
    return len({tuple(sorted(tuple(x for t, x in enumerate(c) if t != axis) for c in star if c[axis] == v)) for v in range(4)})
print("distinct slice patterns per axis", [pats(a) for a in range(3)])
