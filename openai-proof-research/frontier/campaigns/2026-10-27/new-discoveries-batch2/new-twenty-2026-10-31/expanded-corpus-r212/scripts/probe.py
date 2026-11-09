import importlib.util
for x in ['networkx','sympy','scipy']:print(x,bool(importlib.util.find_spec(x)))
