from ntlib import *
m12 = (10**12 - 1)//(3**3 * 7)
m24 = (10**24 - 1)//(3**3 * 7)
m48 = (10**48 - 1)//(3**3 * 7)
print("m12 =", m12, "=", factorint(m12))
print("m24 factors:", factorint(m24))
print("m48 factors:", factorint(m48))
for M in (m12, m24, m48):
    phi = 1
    for p,e in factorint(M).items(): phi *= (p-1)*p**(e-1)
    print(f"M~1e{len(str(M))-1}: ord(10)={order_fast(10,M,10**12 if M is m12 else 10**24 if M is m24 else 10**48)}, "
          f"ord(3)={order_fast(3,M,phi)}, ord(7)={order_fast(7,M,phi)}, phi={phi}")
for p,e in factorint(m12).items():
    g = set(); x = 1
    o3, o7 = order_fast(3,p,p-1), order_fast(7,p,p-1)
    for u in range(o3):
        for w in range(o7): g.add(x*pow(7,w,p)%p)
        x = x*3%p
    print(f"p={p}: |<3,7>|={len(g)} of {p-1}; ord2={order_fast(2,p,p-1)}")
