from pathlib import Path
import re
L=Path(__file__).resolve().parent
out=['import Mathlib.Data.Rat.Defs','import Mathlib.Data.Fintype.Pi','set_option autoImplicit false','set_option warningAsError true','set_option maxRecDepth 10000','namespace RationalEnumeration','abbrev V := Fin 3 → ℚ']
for tag in ['G','H']:
 text=(L/f'Instance{tag}.lean').read_text()
 for prefix in ['q','p']:
  line=next(x for x in text.splitlines() if x.startswith('def '+prefix+tag+' :'))
  line=line.replace(' → E :=',' → V :=').replace(': ℝ',': ℚ')
  def vec(m):
   entries=m[1].split(',')
   return '(fun k => match k.val with '+''.join('| '+(str(i) if i<len(entries)-1 else '_')+' => '+v+' ' for i,v in enumerate(entries))+')'
  while '![' in line:line=re.sub(r'!\[([^\[\]]*)\]',vec,line)
  out.append(line)
out.extend('''def dt (a b c : V) : ℚ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)
def intersection (a b c : V) : V := fun k =>
  if k = 0 then dt (fun t => if t = 0 then 1 else a t) (fun t => if t = 0 then 1 else b t) (fun t => if t = 0 then 1 else c t) / dt a b c
  else if k = 1 then dt (fun t => if t = 1 then 1 else a t) (fun t => if t = 1 then 1 else b t) (fun t => if t = 1 then 1 else c t) / dt a b c
  else dt (fun t => if t = 2 then 1 else a t) (fun t => if t = 2 then 1 else b t) (fun t => if t = 2 then 1 else c t) / dt a b c
def dot (a b : V) : ℚ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
def valid (q : Fin 32 → V) (p : Fin 60 → V) (i j k : Fin 32) : Prop :=
  i < j → j < k → dt (q i) (q j) (q k) ≠ 0 ∧
    ((∀ t, dot (q t) (intersection (q i) (q j) (q k)) ≤ 1) →
      ∃ v, intersection (q i) (q j) (q k) = p v)
instance (q : Fin 32 → V) (p : Fin 60 → V) (i j k : Fin 32) : Decidable (valid q p i j k) := inferInstanceAs (Decidable (_ → _ → _ ∧ (_ → ∃ _, _)))
theorem completeG : ∀ i j k, valid qG pG i j k := by decide +kernel
theorem completeH : ∀ i j k, valid qH pH i j k := by decide +kernel
end RationalEnumeration
'''.splitlines())
(L/'RationalEnumeration.lean').write_text('\n'.join(out)+'\n')
