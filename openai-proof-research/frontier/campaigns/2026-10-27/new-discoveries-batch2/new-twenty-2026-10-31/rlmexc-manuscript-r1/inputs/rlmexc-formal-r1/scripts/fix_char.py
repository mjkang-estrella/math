import re
p='Characterization.lean';s=open(p).read()
vs=[0,4,5,6,8];tails=[[5,0,4,8,6],[5,0,8,4,6],[5,8,0,4,6],[0,5,4,8,6],[0,5,8,4,6],[8,5,0,4,6],[0,5,4,6,8],[5,0,4,6,8]]
for i,t in enumerate(tails):
 a=[1,2,3]+t+[7];q=[a.index(j) for j in range(9)]
 start=f'    · have hp : pi.symm = p{i}.symm := by\n'
 b=s.index(start);e=s.index('      have : pi =',b)
 r=start+'        apply Equiv.ext\n        intro v\n        apply Fin.ext\n        fin_cases v\n'
 for j in range(9):r+=f'        · change (pi.symm ({j} : Fin 9)).val = {q[j]}\n          omega\n'
 s=s[:b]+r+s[e:]
open(p,'w').write(s)
