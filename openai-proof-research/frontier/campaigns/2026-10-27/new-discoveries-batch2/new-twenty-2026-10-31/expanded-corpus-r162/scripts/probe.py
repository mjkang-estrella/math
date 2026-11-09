import importlib.util
for m in ['sympy','networkx','scipy','z3','pysat']:print(m, bool(importlib.util.find_spec(m)))
