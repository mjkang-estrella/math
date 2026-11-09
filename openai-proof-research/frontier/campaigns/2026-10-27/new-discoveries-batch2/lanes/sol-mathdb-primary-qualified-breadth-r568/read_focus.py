import pathlib
D=pathlib.Path(__file__).resolve().parent
for name,a,b in [('2308.06670',40000,45500),('2401.11496',-18000,-12000),('2407.07553',0,2500)]:
 t=(D/(name+'.html.txt')).read_text();print('\n',name,'\n',t[a:b])
t=(D/'2407.07553.html.txt').read_text()
for q in ['Conjecture','conjecture','A.5 Proof']:
 start=0
 for i in range(5):
  k=t.find(q,start)
  if k<0:break
  print(q,t[max(0,k-150):k+1300]);start=k+len(q)
