import sys
src = open('compute.py').read().replace('NMAX = 26','NMAX = 34').replace('for n in range(13):','for n in range(0):')
exec(src)
print("k | n : Delta_{i+j+2k} positive-coeff? (direct Hankel det)")
res = {}
for k in range(1,5):
    line = []
    for n in range(1,8):
        if 2*k + 2*(n-1) + 1 >= 34: line.append("?"); continue
        D = hankel_det(2*k, n)
        line.append("Y" if pzero(D) else "N")
    print(k, line)
# odd shifts for contrast
print("odd shifts r=3,5 (n<=4):")
for r in (3,5):
    line = []
    for n in range(1,5):
        D = hankel_det(r, n)
        line.append("Y" if pzero(D) else "N")
    print(r, line)
