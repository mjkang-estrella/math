import itertools
vs=[0,4,5,6,8]
sol=[]
for p in itertools.permutations(range(3,8)):
 a,b,c,d,e=p
 if a<b<d and b>=4 and d>=6 and c<=4:sol.append(p)
print(sol)
f=open('Arithmetic.lean','w');f.write('import Mathlib.Tactic\nnamespace AK350721\ntheorem tail_arithmetic (a b c d e : ℕ)\n')
for x in 'abcde':f.write(f'    (h{x} : 3 ≤ {x} ∧ {x} ≤ 7)\n')
for x,y in itertools.combinations('abcde',2):f.write(f'    (h{x}{y} : {x} ≠ {y})\n')
f.write('    (hab : a < b) (hbd : b < d) (hb4 : 4 ≤ b) (hd6 : 6 ≤ d) (hc4 : c ≤ 4) :\n')
f.write(' ∨\n'.join('    ('+' ∧ '.join(f'{x} = {v}' for x,v in zip('abcde',p))+')' for p in sol))
f.write(' := by\n  omega\nend AK350721\n')
f.close()
