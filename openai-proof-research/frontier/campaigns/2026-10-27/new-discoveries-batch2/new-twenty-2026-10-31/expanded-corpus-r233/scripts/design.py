import pathlib,json
P=pathlib.Path(__file__).resolve().parents[1];count=0;survive=[]
# Source Case 5: r>k; necessary conditions only, not a design existence test.
for k in range(2,151):
 for y in range(1,k//2+1):
  for r in range(k+1,1001):
   num=(y-1)*(r-1)
   if num%(k-1):continue
   lam=1+num//(k-1)
   if k*lam%y:continue
   if lam*(r-1) < 0:continue
   count+=1
   gap=(k-1)*(r-lam)*((k+r)**2-lam*k)-k*k*lam*lam
   if gap<=0:survive.append([k,r,lam,y,gap])
print(json.dumps({'k_range':[2,150],'r_range':'k+1 through 1000','y_range':'1 through floor(k/2)','necessary_parameter_tuples':count,'M_property_survivors':survive,'scope':'parameter filter only; no enumeration of designs'}))
