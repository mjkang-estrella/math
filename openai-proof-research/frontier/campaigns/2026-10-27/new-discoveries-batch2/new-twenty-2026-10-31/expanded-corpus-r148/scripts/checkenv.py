import importlib.util
for p in ['numpy','scipy','sympy','z3','networkx']:print(p,bool(importlib.util.find_spec(p)))
