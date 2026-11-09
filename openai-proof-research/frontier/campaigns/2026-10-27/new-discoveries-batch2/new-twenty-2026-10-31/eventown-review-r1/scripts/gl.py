import pathlib,json,math
rows=[]
for p in (3,5,7,11,13,17,19,23,29,31):
 # Independent closed-form matrices (-1)^k [[1,k],[0,1]]
 def mat(k):return (((-1)**k)%p, (((-1)**k)*k)%p,0,((-1)**k)%p)
 E=mat(0);F={mat(i) for i in range(p)}
 def order(k):return next(t for t in range(1,2*p+1) if mat(k*t)==E)
 qs={order(i-j) for i in range(p) for j in range(p) if i!=j}
 assert len(F)==p and all(o%p==0 for o in qs) and mat(p) not in F and order(1)==2*p
 rows.append({'p':p,'card':len(F),'order_A':order(1),'quotient_orders':sorted(qs),'A_power_p':mat(p),'nonclosure':True,'sylow_order':p})
pathlib.Path('outputs/independent-gl.json').write_text(json.dumps(rows,indent=2));print(rows)
