from pathlib import Path
import json,shutil
w=Path(__file__).resolve().parent;c=json.loads((w.parent/'fresh-corpus-r10/spectral_candidate.json').read_text());r=json.loads((w/'similarity.json').read_text())
shutil.copyfile(w.parent/'fresh-corpus-r10/AutomatonCertificate.lean',w/'AutomatonCertificate.lean')
f=['import Mathlib.Combinatorics.SimpleGraph.AdjMatrix','import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic','import Mathlib.Data.Rat.Defs','import Mathlib.Tactic.FinCases','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace ActualSpectra330264']
for k in ['g','h']:
 E=c[k];f.append('def edges'+k.upper()+' : List (Nat × Nat) := '+str([tuple(e) for e in E]))
f+=['def adjacent (es : List (Nat × Nat)) (u v : Fin 19) : Prop := (u.val, v.val) ∈ es ∨ (v.val, u.val) ∈ es','instance (es) : DecidableRel (adjacent es) := fun u v => inferInstanceAs (Decidable ((u.val, v.val) ∈ es ∨ (v.val, u.val) ∈ es))','def graph (es : List (Nat × Nat)) (hs : ∀ v : Fin 19, ¬ adjacent es v v) : SimpleGraph (Fin 19) where','  Adj := adjacent es','  symm := ⟨fun _ _ h => h.symm⟩','  loopless := ⟨hs⟩','def G : SimpleGraph (Fin 19) := graph edgesG (by decide +kernel)','def H : SimpleGraph (Fin 19) := graph edgesH (by decide +kernel)','instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent edgesG _ _))','instance : DecidableRel H.Adj := fun _ _ => inferInstanceAs (Decidable (adjacent edgesH _ _))', 'def AG : Matrix (Fin 19) (Fin 19) ℚ := G.adjMatrix ℚ','def AH : Matrix (Fin 19) (Fin 19) ℚ := H.adjMatrix ℚ','def CG : Matrix (Fin 19) (Fin 19) ℚ := Gᶜ.adjMatrix ℚ','def CH : Matrix (Fin 19) (Fin 19) ℚ := Hᶜ.adjMatrix ℚ']
# Explicit edge-index line graphs; intrinsic edgeSet equivalence remains separate.
for k in ['G','H']:
 f += [f'def edge{k} (i : Fin 18) : Nat × Nat := edges{k}[i.val]!',f'def line{k} : SimpleGraph (Fin 18) where',f'  Adj i j := i ≠ j ∧ ((edge{k} i).1 = (edge{k} j).1 ∨ (edge{k} i).1 = (edge{k} j).2 ∨ (edge{k} i).2 = (edge{k} j).1 ∨ (edge{k} i).2 = (edge{k} j).2)', '  symm := ⟨by intros; aesop⟩','  loopless := ⟨by intro i; simp⟩','instance : DecidableRel line'+k+'.Adj := fun i j => by unfold SimpleGraph.Adj line'+k+'; infer_instance',f'def L{k} : Matrix (Fin 18) (Fin 18) ℚ := line{k}.adjMatrix ℚ']
f+=['theorem charpoly_of_intertwiner {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) ℚ)','    (hp : P * Q = 1) (hq : Q * P = 1) (hi : A * P = P * B) : A.charpoly = B.charpoly := by','  have hA : A = P * (B * Q) := by rw [← Matrix.mul_assoc, ← hi, Matrix.mul_assoc, hp, mul_one]','  rw [hA, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hq, mul_one]']
for name,pre in [('adjacency','A'),('complement','C'),('line','L')]:
 n=18 if pre=='L' else 19
 for t in ['P','Q']:
  rows=r[name][t];f.append(f'def {pre}{t} : Matrix (Fin {n}) (Fin {n}) ℚ := !!['+';\n'.join(', '.join('('+x+')' for x in row) for row in rows)+']')
 for label,expr in [('pq',f'{pre}P * {pre}Q = 1'),('qp',f'{pre}Q * {pre}P = 1'),('intertwine',f'{pre}G * {pre}P = {pre}P * {pre}H')]:
  f.append(f'theorem {pre}_{label} : {expr} := by')
  lhs,rhs=expr.split(' = ')
  for i in range(n): f.append(f'  have r{i} : ∀ j : Fin {n}, ({lhs}) {i} j = ({rhs} : Matrix (Fin {n}) (Fin {n}) ℚ) {i} j := by decide +kernel')
  f.append('  ext i j\n  fin_cases i')
  for i in range(n): f.append(f'  · exact r{i} j')
 f.append(f'theorem {name}_charpoly : {pre}G.charpoly = {pre}H.charpoly := charpoly_of_intertwiner _ _ {pre}P {pre}Q {pre}_pq {pre}_qp {pre}_intertwine')
 f.append(f'#print axioms {name}_charpoly')
f.append('end ActualSpectra330264');(w/'ActualSpectra.lean').write_text('\n'.join(f)+'\n')
