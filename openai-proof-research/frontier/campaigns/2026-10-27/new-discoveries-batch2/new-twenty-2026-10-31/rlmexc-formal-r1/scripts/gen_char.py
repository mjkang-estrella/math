import itertools
vs=[0,4,5,6,8]
tails=[[5,0,4,8,6],[5,0,8,4,6],[5,8,0,4,6],[0,5,4,8,6],[0,5,8,4,6],[8,5,0,4,6],[0,5,4,6,8],[5,0,4,6,8]]
ps=[[1,2,3]+t+[7] for t in tails];qs=[[p.index(j) for j in range(9)] for p in ps]
sol=sorted(tuple(q[v] for v in vs) for q in qs)
f=open('Characterization.lean','w');f.write('''import Concrete
import Arithmetic
namespace AK350721
open Finset

theorem characterization9 (pi : Equiv.Perm (Fin 9)) :
    rlmv pi = R9 ∧ excv pi = E9 ↔
      pi = p0 ∨ pi = p1 ∨ pi = p2 ∨ pi = p3 ∨ pi = p4 ∨ pi = p5 ∨ pi = p6 ∨ pi = p7 := by
  constructor
  · rintro ⟨hr, he⟩
    obtain ⟨h1, h2, h3, h7⟩ := forced9 pi hr he
    have lo (v : Fin 9) (hv : v ≠ 1 ∧ v ≠ 2 ∧ v ≠ 3 ∧ v ≠ 7) :
        3 ≤ (pi.symm v).val ∧ (pi.symm v).val ≤ 7 := by
      have hne1 := Fin.val_injective.ne (pi.symm.injective.ne hv.1)
      have hne2 := Fin.val_injective.ne (pi.symm.injective.ne hv.2.1)
      have hne3 := Fin.val_injective.ne (pi.symm.injective.ne hv.2.2.1)
      have hne7 := Fin.val_injective.ne (pi.symm.injective.ne hv.2.2.2)
      rw [h1] at hne1
      rw [h2] at hne2
      rw [h3] at hne3
      rw [h7] at hne7
      have := (pi.symm v).isLt
      omega
    have ex (v : Fin 9) : pi.symm v < v ↔ v ∈ E9 := by
      rw [← he]; simp [excv]
    have ne4 : 4 ≤ (pi.symm 4).val := by
      have h := (ex 4).not.mpr (by decide)
      exact Nat.le_of_not_gt h
    have ne6 : 6 ≤ (pi.symm 6).val := by
      have h := (ex 6).not.mpr (by decide)
      exact Nat.le_of_not_gt h
    have ex5 : (pi.symm 5).val ≤ 4 := by
      have h := (ex 5).mpr (by decide)
      omega
    have o04 := minima_positions pi (show 0 ∈ rlmv pi by rw [hr]; decide)
      (show 4 ∈ rlmv pi by rw [hr]; decide) (by decide)
    have o46 := minima_positions pi (show 4 ∈ rlmv pi by rw [hr]; decide)
      (show 6 ∈ rlmv pi by rw [hr]; decide) (by decide)
    have h := tail_arithmetic''')
for v in vs:f.write(f' (pi.symm {v}).val')
for v in vs:f.write(f'\n      (lo {v} (by decide))')
for u,v in itertools.combinations(vs,2):f.write(f'\n      (Fin.val_injective.ne (pi.symm.injective.ne (show ({u} : Fin 9) ≠ {v} by decide)))')
f.write('\n      o04 o46 ne4 ne6 ex5\n    rcases h with h | h | h | h | h | h | h | h\n')
for soln in sol:
 i=next(i for i,q in enumerate(qs) if tuple(q[v] for v in vs)==soln)
 f.write(f'''    · have hp : pi.symm = p{i}.symm := by
        ext v
        fin_cases v <;> apply Fin.ext <;>
          simp only [p{i}, Equiv.symm_mk, Equiv.coe_fn_mk, Matrix.cons_val_zero,
            Matrix.cons_val_succ, Matrix.head_cons, Matrix.head_fin_const] <;> omega
      have : pi = p{i} := Equiv.symm_injective hp
      tauto
''')
f.write('''  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
''')
for i in range(8):f.write(f'    · exact p{i}_sets\n')
f.write('end AK350721\n');f.close()
