import json
n=785;M=5**10
full=[1]
for t in range(2*n):
 z=[0]*(t+2)
 for h,v in enumerate(full):
  z[h+1]+=v*(2*h+1)**2
  if h:z[h-1]+=v
 full=z
x=full[0];v=0
while x%5==0:x//=5;v+=1
trunc=[1]+[0]*17
for t in range(2*n):
 z=[0]*18
 for h,x in enumerate(trunc):
  if h<17:z[h+1]=(z[h+1]+x*(2*h+1)**2)%M
  if h:z[h-1]=(z[h-1]+x)%M
 trunc=z
print(json.dumps({'n':n,'full_integer_valuation':v,'full_integer_mod_5pow10':full[0]%M,'height_17_transfer_mod_5pow10':trunc[0],'agree':full[0]%M==trunc[0],'predicted_from_literal_alpha_15over4':8,'digits':len(str(full[0]))}))
