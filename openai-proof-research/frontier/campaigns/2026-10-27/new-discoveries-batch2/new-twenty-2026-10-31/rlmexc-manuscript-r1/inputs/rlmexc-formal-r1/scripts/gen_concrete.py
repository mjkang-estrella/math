tails=[[5,0,4,8,6],[5,0,8,4,6],[5,8,0,4,6],[0,5,4,8,6],[0,5,8,4,6],[8,5,0,4,6],[0,5,4,6,8],[5,0,4,6,8]]
f=open('Concrete.lean','w');f.write('import Finite\nnamespace AK350721\nopen Finset\n')
for i,t in enumerate(tails):
 p=[1,2,3]+t+[7];q=[p.index(j) for j in range(9)]
 vec=lambda a:'!['+', '.join(map(str,a))+']'
 f.write(f'def p{i} : Equiv.Perm (Fin 9) where\n  toFun := {vec(p)}\n  invFun := {vec(q)}\n  left_inv := by decide\n  right_inv := by decide\n')
 f.write(f'theorem p{i}_sets : rlmv p{i} = R9 ∧ excv p{i} = E9 := by decide\n')
 inv=sum(p[a]>p[b] for a in range(9) for b in range(a+1,9))
 f.write(f'theorem p{i}_inv : invCount p{i} = {inv} := by decide\n')
 f.write(f'theorem p{i}_cycle : '+('' if i in [0,1,2,4,5] else '¬ ')+f'cycleGe 3 p{i} := by\n  unfold cycleGe\n  decide\n')
f.write('end AK350721\n');f.close()
