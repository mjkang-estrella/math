#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Exact diagnostic witnesses, not a proof."""
from fractions import Fraction as Q
from checked_run import failed
import json


def main():
    # Recentering on a represented endpoint needs radius two, not one.
    points = [Q(-1), Q(1)]
    assert all(abs(x) <= 1 for x in points)
    assert all(max(abs(x-z) for x in points) == 2 for z in points)
    # Weak separation at twice the radius does not imply packing injectivity.
    assert abs(points[0]-points[1]) == 2
    # Enlarging the multiplicative window by one dyadic power admits one extra index.
    assert all(Q(1,8) < Q(1,2**k) <= 1 for k in [0,1,2])
    assert Q(1) <= 2**3*Q(1,8) and 3 > 2
    # The metric cluster constant is attained by two shifted endpoints on R.
    assert abs(Q(99,50)-Q(101,100)) == Q(97,200)*2 < Q(1,2)*2
    assert Q(1,32)**2 <= 2*(2*Q(1,64))**2 and not Q(1,32)<Q(1,64)
    assert 65+16 == 81 > 80
    assert 76800**2 == 5898240000
    assert failed(0,'SOME FAIL','') and failed(0,'','error: diagnostic')
    assert failed(1,'','') and not failed(0,'PASS','')
    print(json.dumps({'status':'PASS exact semantic witnesses and runner predicates',
                      'universal_proofs':'Lean source; finite diagnostics are not universal proofs',
                      'full_CDF098_formalized':False},sort_keys=True))


if __name__ == '__main__':
    main()
