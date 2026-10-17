#!/usr/bin/env python3
# Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
# Original task-local bounded diagnostic. It does not prove O234.
import itertools, json
from fractions import Fraction as Q

def main():
    h=((1,1,1,1),(1,-1,1,-1),(1,1,-1,-1),(1,-1,-1,1))
    u=[[Q(v,2) for v in row] for row in h]
    assert all(sum(u[i][l]*u[j][l] for l in range(4)) == int(i==j)
               for i in range(4) for j in range(4))
    base=[Q(1,3),Q(1,3),Q(-1,2),Q(-2,3)]
    spike=Q(5,4)
    passed=0; false_variant=[]
    for sigma in itertools.product((-1,1),repeat=4):
        x=[sum(u[i][j]*sigma[j] for j in range(4)) for i in range(4)]
        energy0=sum(base[i]*x[i]**2 for i in range(4))/2
        rank2=energy0+spike*(x[0]**2+x[1]**2)/2
        # Exact two-coordinate covering: y1^2+y2^2 <=2 max(y1^2,y2^2).
        rank1=[energy0+spike*x[i]**2 for i in range(2)]
        assert rank2<=max(rank1)
        passed+=1
        if rank2>max(energy0+spike*x[i]**2/2 for i in range(2)):
            false_variant.append(list(sigma))
    assert false_variant
    # Equal-dimensional flat-block rotations preserve trace-square of the spike;
    # absent flatness this fails already for diagonal base(0,1).
    assert Q(1)**2+Q(1)**2 != Q(0)**2+Q(2)**2
    return {'status':'FINITE_DIAGNOSTICS_ONLY','orthogonality_exact':True,
            'spin_configurations':passed,'weakened_strength_counterexamples':false_variant,
            'nonflat_direction_swap_trace_square_mismatch':True,
            'universal_theorem_certified':False}
if __name__=='__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
