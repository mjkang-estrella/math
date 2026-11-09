import importlib.util
for m in ['networkx','sympy','numpy','scipy']:
 print(m,importlib.util.find_spec(m))
