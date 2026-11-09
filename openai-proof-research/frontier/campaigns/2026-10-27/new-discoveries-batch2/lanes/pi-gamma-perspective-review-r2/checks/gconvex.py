import sympy as sp
u = sp.symbols('u', positive=True)
g = -sp.log(1 - u**-2)
g2 = sp.simplify(sp.diff(g, u, 2))
print("g'' =", sp.factor(g2))
num = sp.factor(sp.together(g2).as_numer_denom()[0])
den = sp.factor(sp.together(g2).as_numer_denom()[1])
print("num factor:", num)
print("den factor:", den)
