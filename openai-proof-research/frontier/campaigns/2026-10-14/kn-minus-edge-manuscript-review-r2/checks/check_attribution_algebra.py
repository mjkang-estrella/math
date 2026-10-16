#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Independent exact arithmetic for the revised attribution; no paper imports."""
from fractions import Fraction
from pathlib import Path
import json

OWN=Path(__file__).resolve().parents[1]


def product(values):
    answer=1
    for v in values: answer*=v
    return answer


def z(n):
    return Fraction(product((n-i)//2 for i in range(4)),4)


def minus(n):
    t=(n-1)//2
    return z(n)-t*(t-1)//2


def printed_a(n):
    return Fraction(product((n+i)//2 for i in (2,-1,-3,-4)),4)


def printed_b(m,n):
    return Fraction(product((m+i)//2 for i in (1,-1,-2)),4)*(n*((m+4)//2)+(m-4)//2)


def main():
    orders=list(range(2,1001))+[10**101+i for i in range(4)]
    for n in orders:
        assert minus(n)==printed_a(n) and minus(n).denominator==1
    bases=list(range(4,301))+[10**101+i for i in range(4)]
    lengths=[1,2,3,17,10**99]
    for m in bases:
        for n in lengths:
            assert printed_b(m,n)==(n-1)*minus(m+2)+2*z(m+1)
        assert printed_b(m,1)==2*z(m+1)
        # The product's sensitivity to a changed minus-edge input is exactly n-1.
        for n in lengths:
            delta=(n-1)*(minus(m+2)+37)+2*z(m+1)-printed_b(m,n)
            assert delta==37*(n-1)
    for s in range(2,501):
        n=2*s+1
        old_bound=(2*z(n-1)+(n-2)*(z(n)-(n-3)//2))/n
        gap=minus(n)-old_bound
        assert gap==Fraction((s-1)*(s-2),2*(2*s+1))
        assert (gap<1)==(s<=6)
    assert minus(15)==420 and z(14)==315
    assert printed_b(13,1)==630 and printed_b(13,2)==1050
    assert 419+2*z(14)==1049
    receipt=dict(status='PASS',theorem_orders=len(orders),product_bases=len(bases),
                 path_lengths=[str(n) for n in lengths],odd_gap_cases=499,
                 n1_minus_edge_sensitivity=0,n2_minus_edge_sensitivity=1,
                 examples={'m13_n1':630,'m13_n2':1050,'weaker_n2_lower_bound':1049},
                 arithmetic='integers and fractions.Fraction only',
                 scope='Independent finite identities and coefficient sensitivity; no new full proof or source/priority conclusion.')
    (OWN/'receipts/attribution-algebra.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
