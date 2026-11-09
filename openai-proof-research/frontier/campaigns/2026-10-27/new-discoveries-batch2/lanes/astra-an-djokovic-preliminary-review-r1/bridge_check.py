"""Exact finite check of reviewer bridge (B), using independent path DP."""
import sys
sys.dont_write_bytecode=True
from independent_check import monomial_ds
from itertools import product
from math import comb
from pathlib import Path
import json

def bridge(a):
    n=len(a)
    return (-1)**(n-1)+sum((-1)**(n-j-1)*comb(n,j)
        for j in range(1,n) if sum(a[:j])>=j)

rows=[]
for n in range(2,7):
    count=0
    for middle in product((0,1),repeat=n-2):
        for first in range(n-sum(middle)):
            a=(first,*middle,n-1-first-sum(middle))
            assert monomial_ds(a)==bridge(a);count+=1
    rows.append({'n':n,'basis_vectors':count})
bad=(0,2,0)
assert monomial_ds(bad)!=bridge(bad)
Path(__file__).with_name('bridge-check-results.json').write_text(json.dumps({
    'status':'PASS (finite checks only)','rows':rows,
    'negative_control':{'exponents':bad,'violates_internal_degree_bound':True,
      'actual_DS':str(monomial_ds(bad)),'invalid_bridge_value':bridge(bad)}},indent=2)+'\n')
print(rows,'negative control',monomial_ds(bad),bridge(bad))
