import json,pathlib
P=pathlib.Path(__file__).parent
out=[]
for n in range(3,11):
 values=[sum(((x>>i)&1)*((x>>((i+1)%n))&1)*((x>>((i+2)%n))&1) for i in range(n))%2 for x in range(1<<n)]
 a=[1-2*v for v in values];step=1
 while step<len(a):
  for i in range(0,len(a),2*step):
   for k in range(i,i+step):x,y=a[k],a[k+step];a[k],a[k+step]=x+y,x-y
  step*=2
 weight=sum(values);nonlinearity=((1<<n)-max(map(abs,a)))//2
 assert weight==nonlinearity
 out.append({'n':n,'weight':weight,'nonlinearity':nonlinearity,'walsh_zero':a[0],'max_abs_nonzero_walsh':max(map(abs,a[1:]))})
# Exterior basis 1,e1,e2,e1e2. Left multiplying by e1 yields [0,a,0,c].
# Therefore e1*u can never equal e2: its e2 coefficient is always zero.
def exterior(a,b):
 if a&b:return (0,0)
 inversions=sum(1 for i in range(2) for k in range(2) if (a>>i)&1 and (b>>k)&1 and i>k)
 return (-1 if inversions%2 else 1,a|b)
products=[exterior(1,b) for b in range(4)]
assert products==[(1,1),(0,0),(1,3),(0,0)]
assert all(sign==0 or mask!=2 for sign,mask in products)
(P/'masuda-basis-products.json').write_text(json.dumps({'executed':True,'basis_masks':[0,1,2,3],'left_e1_products_sign_and_mask':products,'no_product_has_e2_component':True,'published_example_only':True},indent=2)+'\n')
(P/'bounded-calculations.json').write_text(json.dumps({'executed':True,'boolean_instances':out,'masuda_coefficient_obstruction':{'basis':['1','e1','e2','e1e2'],'e1_times_u_coefficients':['0','a','0','c'],'required_e2_coefficient':1,'actual_e2_coefficient':0},'credit':0,'limit':'Instances and elementary replay of already published counterexample; no all-n independent proof or discovery.'},indent=2)+'\n')
