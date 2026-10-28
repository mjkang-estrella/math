import sympy as sp

w1,w2,w3 = sp.symbols('w1 w2 w3', positive=True)
a,b,a2,b2 = sp.symbols('a b a2 b2')   # complex entries, conj(a)=ab etc.
def cb(s):
    return sp.Symbol(str(s)+'b') if isinstance(s, sp.Symbol) else s
def conj(e):
    return sp.expand(e).xreplace({s: sp.Symbol(str(s)+'b') for s in [a,b,a2,b2]})

n=3
w={1:w1,2:w2,3:w3}
def compute(Xd, Yd):
    Xe = {(i,j):sp.Integer(0) for i in range(1,4) for j in range(1,4)}
    Ye = dict(Xe)
    for k,v in Xd.items(): Xe[k]=sp.sympify(v)
    for k,v in Yd.items(): Ye[k]=sp.sympify(v)
    T = {}
    for i in range(1,4):
        for j in range(1,4):
            T[i,j] = sp.expand(sum(w[k]*(Xe[i,k]*Ye[k,j]-Ye[i,k]*Xe[k,j]) for k in range(1,4)))
    Tn2 = sum(T[i,j]*conj(T[i,j]) for i in range(1,4) for j in range(1,4))
    X2 = sum(Xe[i,j]*conj(Xe[i,j]) for i in range(1,4) for j in range(1,4))
    Y2 = sum(Ye[i,j]*conj(Ye[i,j]) for i in range(1,4) for j in range(1,4))
    XY = sum(Xe[i,j]*conj(Ye[i,j]) for i in range(1,4) for j in range(1,4))
    c2 = w1**2+w2**2
    D = sp.expand(c2*X2*Y2 - c2*XY*conj(XY) - Tn2)
    return sp.factor(D)

# Family 1: X = E12 + a E13, Y = E21 + b E31
D1 = compute({(1,2):1,(1,3):a}, {(2,1):1,(3,1):b})
print("D1 =", D1)
# Family 2: X = E12 + a E23, Y = E21 + b E32
D2 = compute({(1,2):1,(2,3):a}, {(2,1):1,(3,2):b})
print("D2 =", D2)
# Family 3: X = E12 + a E13, Y = E21 + b E32
D3 = compute({(1,2):1,(1,3):a}, {(2,1):1,(3,2):b})
print("D3 =", D3)
# Family 4: X = E12 + a E13, Y = E12 + b E13 (parallel-ish, <X,Y> != 0)
D4 = compute({(1,2):1,(1,3):a}, {(1,2):1,(1,3):b})
print("D4 =", D4)
# Family 5: X = E12 + a E11, Y = E21 + b E22
D5 = compute({(1,2):1,(1,1):a}, {(2,1):1,(2,2):b})
print("D5 =", D5)
