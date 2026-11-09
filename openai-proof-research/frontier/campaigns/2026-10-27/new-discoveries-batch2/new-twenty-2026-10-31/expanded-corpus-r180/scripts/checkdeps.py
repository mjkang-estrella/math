import importlib.util
for x in ['scipy','numpy','networkx','z3','sympy']:print(x,bool(importlib.util.find_spec(x)))
