# Independent brute-force check (Stanley subset expansion over all 2^16 edge subsets) of the c=5, n=16 CSF collision.
import sys, os
sys.argv = ['csf.py', '16', '5']
__file__ = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'csf_selftest.py')
src = open(__file__).read().split('cnt = 0')[0]
exec(src)
A = ((1, 0), (2, 0), (2, 0), (4, 2), (7, 9)); B = ((1, 0), (3, 0), (2, 0), (2, 0), (8, 57))
ba, bb = brute(A), brute(B)
print('brute equal:', ba == bb, '| dp equal:', csf(A) == csf(B), '| dp==brute:', csf(A) == ba and csf(B) == bb, '| terms', len(ba))
print('invariants', invariants(A), invariants(B))
