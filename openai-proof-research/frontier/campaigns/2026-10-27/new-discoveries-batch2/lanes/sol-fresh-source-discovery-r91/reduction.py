import sympy as s,json,pathlib
z,t,x=s.symbols('z t x');M=s.Matrix([[z,1+z,1+z],[0,1+z,z],[z+z*z,0,1+z]]);v=s.Matrix([z**4+2*z**3,z**4,2*z**4+2*z**3]);F=s.factor((s.ones(1,3)*(s.eye(3)-t*M).inv()*v)[0]);print('char',s.factor(M.charpoly(x).as_expr()));print('GF',F)
for i in range(7):print(i+4,[s.expand(p) for p in v],s.expand(sum(v)));v=M*v
