import pathlib,json,sys
L=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);out=[]
for k in range(int(sys.argv[2]) if len(sys.argv)>2 else 1,130 if len(sys.argv)>2 else 66,4):
 Y=2*N//k+1;side=N+1;p=bytearray(side*side*Y);states=bad=interior=0;first=[]
 for x in range(side):
  for z in range(side):
   base=(x*side+z)*Y
   for y in range((x+z)//k+1):
    lose=True
    for u in range(x):
     if p[(u*side+z)*Y+min(y,(u+z)//k)]:lose=False;break
    if lose:
     for v in range(y):
      if p[base+v]:lose=False;break
    if lose:
     for w in range(z):
      if p[(x*side+w)*Y+min(y,(x+w)//k)]:lose=False;break
    p[base+y]=lose;states+=1
    if lose!=(((x-1)^y^(z-1))==0):
     bad+=1
     if x and z:
      interior+=1
      if len(first)<5:first.append([x,y,z,bool(lose)])
  
 r=dict(k=k,N=N,states=states,mismatches=bad,positive_xz_mismatches=interior,first=first);out.append(r);print(r,flush=True)
(L/f'chocolate-{N}.json').write_text(json.dumps(out,indent=2))
