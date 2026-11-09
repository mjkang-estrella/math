p='Concrete.lean';s=open(p).read();s=s[:s.rindex('end AK350721')]
tails=[[5,0,4,8,6],[5,0,8,4,6],[5,8,0,4,6],[0,5,4,8,6],[0,5,8,4,6],[8,5,0,4,6],[0,5,4,6,8],[5,0,4,6,8]]
for i,t in enumerate(tails):
 a=[1,2,3]+t+[7];seen=set();lens=[]
 for j in range(9):
  if j in seen:continue
  k=j;m=0
  while k not in seen:seen.add(k);m+=1;k=a[k]
  lens.append(m)
 lens.sort(reverse=True)
 s+=f'theorem p{i}_partition : p{i}.partition.parts = (['+', '.join(map(str,lens))+'] : List ℕ).toMultiset := by decide\n'
s+='end AK350721\n';open(p,'w').write(s)
