from ntlib import *
m12 = (10**12-1)//27; m24 = (10**24-1)//27; m48 = (10**48-1)//27
def phi_of(M):
    r = 1
    for p,e in factorint(M).items(): r *= (p-1)*p**(e-1)
    return r
for name, M, go in (("m12",m12,10**13),("m24",m24,10**24),("m48",m48,10**50)):
    phi = phi_of(M)
    o3, o7, o10 = order_fast(3,M,phi), order_fast(7,M,phi), order_fast(10,M,phi)
    print(f"{name}: phi={phi}, ord3={o3}, ord7={o7}, ord10={o10}")
    if name=="m24":
        print("   lambda24 =", o3//9900, " mu24 =", o7//900)
    if name=="m48":
        print("   lambda48/lambda24 =", o3//849915000, " mu48/mu24 =", o7//673200)
# new primes at each stage and their parameters
prev = set()
for name, M in (("m12",m12),("m24",m24),("m48",m48)):
    fs = factorint(M)
    new = set(fs) - prev
    for p in sorted(new):
        phi = p-1
        o3, o7, o10 = order_fast(3,p,phi), order_fast(7,p,phi), order_fast(10,p,phi)
        print(f"  stage {name} new prime {p}: ord10={o10} ord3={o3} ord7={o7}")
    prev |= set(fs)
print("factor 9999999900000000 =", factorint(9999999900000000))
print("factor 99990000 =", factorint(99990000))
