from pathlib import Path
import itertools
O=Path(__file__).resolve().parent;E=list(itertools.combinations(range(5),2));T=[tuple(E.index(e) for e in itertools.combinations(t,2)) for t in itertools.combinations(range(5),3)];ns='abcdefghij';P=['code '+' '.join(ns[e] for e in t) for t in T];pairs=list(itertools.combinations(range(10),2));defs=[]
for d in range(10,-1,-1):
 body='false' if d==10 else 'all4 fun '+ns[d]+' => check'+str(d+1)+' '+' '.join(ns[:d+1])
 for i,j in reversed(pairs):
  if max(T[i]+T[j])==d-1:body=f'if ({P[i]}) = ({P[j]}) then true else '+body
 defs.append(f'def check{d} '+(' '.join(f'({a} : C)' for a in ns[:d]))+f' : Bool :=\n  {body}\n')
t='import BoolProbe\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\nset_option warningAsError true\nnamespace Palette\n'+'\n'.join(defs)+'\ntheorem check_pass : check0 = true := by decide\nend Palette\n';(O/'Checker.lean').write_text(t)
conds=[f'({P[i]}) ≠ ({P[j]})' for i,j in pairs]
s='import Checker\nimport Mathlib.Data.Fintype.Prod\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\nset_option warningAsError true\nnamespace Palette\n'
s+='theorem code_no '+ ' '.join(f'({a} : C)' for a in ns)+' (hc : '+' ∧ '.join(conds)+') : False := by\n'
s+='  rcases hc with ⟨'+','.join(f'p{k}' for k in range(45))+'⟩\n  have hh0 : check0 = true := check_pass\n'
for d in range(11):
 ps=[f'ite_eq_right p{k}' for k,(i,j) in enumerate(pairs) if max(T[i]+T[j])==d-1]
 s+='  simp only [check'+str(d)+(' , '+', '.join(ps) if ps else '')+f'] at hh{d}\n'
 if d<10:s+=f'  have hh{d+1} := (all4_spec _).mp hh{d} {ns[d]}\n'
 else:s+='  exact Bool.false_ne_true hh10\n'
s+='\nabbrev Triangle (n : Nat) := { t : Fin n × Fin n × Fin n // t.1 < t.2.1 ∧ t.2.1 < t.2.2 }\n'
s+='abbrev Edge (n : Nat) := {p : Fin n × Fin n // p.1 < p.2}\ndef trianglePalette {n k : Nat} (c : Edge n → Fin k) (t : Triangle n) : Finset (Fin k) :=\n  {c ⟨(t.val.1,t.val.2.1),t.property.1⟩, c ⟨(t.val.1,t.val.2.2),lt_trans t.property.1 t.property.2⟩, c ⟨(t.val.2.1,t.val.2.2),t.property.2⟩}\n'
Ts=list(itertools.combinations(range(5),3))
for i,(a,b,c) in enumerate(Ts):s+=f'def t{i} : Triangle 5 := ⟨({a},{b},{c}), by decide⟩\n'
args=[f'c ⟨({i},{j}),by decide⟩' for i,j in E]
s+='theorem no_four (c : Edge 5 → C) : ¬ Function.Injective (trianglePalette c) := by\n  intro hd\n  apply code_no '+' '.join('('+a+')' for a in args)+'\n  refine ⟨' + ', '.join('?_ ' for _ in range(45))+'⟩\n'
for i,j in pairs:
 lhs=' '.join('('+args[e]+')' for e in T[i]);rhs=' '.join('('+args[e]+')' for e in T[j]);
 s+='  · intro he\n    have hp := code_sound '+lhs+' '+rhs+' he\n'
 s+=f'    have ht : t{i} = t{j} := hd hp\n    exact (by decide : t{i} ≠ t{j}) ht\n'
s+='\ndef Achievable (n k : Nat) : Prop := ∃ c : Edge n → Fin k, Function.Injective (trianglePalette c)\n'
s+='def SourceClaim : Prop := ∀ n : Nat, 4 ≤ n → IsLeast {k : Nat | Achievable n k} (n-1)\n'
s+='theorem source_refutation : ¬ SourceClaim := by\n  intro h\n  obtain ⟨c, hc⟩ := (h 5 (by decide)).1\n  exact no_four c hc\nend Palette\n'
(O/'Endpoint.lean').write_text(s)
