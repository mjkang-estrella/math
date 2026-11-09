import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];o=json.loads((D/'outputs/word-certificate.json').read_text())
s='''import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Nonchalant
abbrev Word := List (Fin 3)
-- Positions are zero based. The suffix length s orders positions from right to left.
def insert (w : Word) (s : Nat) (a : Fin 3) : Word :=
  w.take (w.length - s) ++ [a] ++ w.drop (w.length - s)
def SquareFree (w : Word) : Prop :=
  ∀ i ∈ List.range (w.length + 1), ∀ d ∈ List.range (w.length + 1),
    0 < d → i + 2*d ≤ w.length →
      (w.drop i).take d ≠ (w.drop (i+d)).take d
instance (w : Word) : Decidable (SquareFree w) := inferInstanceAs (Decidable (∀ i ∈ List.range (w.length+1), ∀ d ∈ List.range (w.length+1), 0<d → i+2*d≤w.length → (w.drop i).take d ≠ (w.drop (i+d)).take d))
theorem squareFree_iff (w : Word) : SquareFree w ↔
    ∀ i d : Nat, 0 < d → i+2*d ≤ w.length →
      (w.drop i).take d ≠ (w.drop (i+d)).take d := by
  constructor
  · intro h i d hd hb
    exact h i (List.mem_range.mpr (by omega)) d (List.mem_range.mpr (by omega)) hd hb
  · intro h i _ d _ hd hb
    exact h i d hd hb
-- This is the literal rightmost-position, earliest-letter rule, with no search cutoff.
def Step (w v : Word) : Prop :=
  ∃ s ∈ List.range (w.length+1), ∃ a : Fin 3,
    v = insert w s a ∧ SquareFree v ∧
    ∀ t ∈ List.range (w.length+1), ∀ b : Fin 3,
      (t < s ∨ (t = s ∧ b < a)) → ¬ SquareFree (insert w t b)
instance (w v : Word) : Decidable (Step w v) := inferInstanceAs (Decidable (∃ s ∈ List.range (w.length+1), ∃ a : Fin 3, v=insert w s a ∧ SquareFree v ∧ ∀ t ∈ List.range (w.length+1), ∀ b : Fin 3, (t<s ∨ (t=s ∧ b<a)) → ¬ SquareFree (insert w t b)))
theorem step_unique {w v z : Word} (h : Step w v) (k : Step w z) : v = z := by
  obtain ⟨s, hs, a, hv, hf, hm⟩ := h
  obtain ⟨t, ht, b, hz, hg, hn⟩ := k
  have he : s = t := by
    by_contra hne
    by_cases hlt : s < t
    · exact hn s hs a (Or.inl hlt) (hv ▸ hf)
    · exact hm t ht b (Or.inl (by omega)) (hz ▸ hg)
  subst t
  have hab : a = b := by
    apply Fin.ext
    by_contra hne
    by_cases hlt : a < b
    · exact hn s hs a (Or.inr ⟨rfl,hlt⟩) (hv ▸ hf)
    · exact hm s hs b (Or.inr ⟨rfl,by omega⟩) (hz ▸ hg)
  subst b
  exact hv.trans hz.symm
def internalExtensions (w : Word) : List Word :=
  (((List.range (w.length-1)).flatMap fun s =>
    (List.finRange 3).map fun a => insert w (s+1) a).filter fun v => decide (SquareFree v)).eraseDups
def potential (w : Word) : Nat := (internalExtensions w).length
def InfiniteFrom (w : Word) : Prop :=
  ∃ f : Nat → Word, f 0 = w ∧ ∀ n, Step (f n) (f (n+1))
def SourceConjecture : Prop :=
  ∀ w : Word, SquareFree w → 2 < potential w → InfiniteFrom w
'''
for i,w in enumerate(o['path']):s+=f"def w{i} : Word := [{', '.join(str(int(c)-1) for c in w)}]\n"
s+='theorem seed_squarefree : SquareFree w0 := by decide\ntheorem seed_potential : potential w0 = 3 := by decide\n'
for i in range(21):s+=f'theorem move{i} : Step w{i} w{i+1} := by decide\n'
s+='''theorem terminal : ∀ s ∈ List.range (w21.length+1), ∀ a : Fin 3,
    ¬ SquareFree (insert w21 s a) := by decide
theorem no_terminal_step (v : Word) : ¬ Step w21 v := by
  rintro ⟨s,hs,a,hv,hf,_⟩
  exact terminal s hs a (hv ▸ hf)
theorem finite_trajectory : ¬ InfiniteFrom w0 := by
  rintro ⟨f,h0,h⟩
'''
for i in range(21):
 prev='h0' if i==0 else f'e{i}'
 s+=f'  have e{i+1} : f {i+1} = w{i+1} := by\n    have hh := h {i}\n    rw [{prev}] at hh\n    exact step_unique hh move{i}\n'
s+='''  have hh := h 21
  rw [e21] at hh
  exact no_terminal_step (f 22) hh
theorem source_refutation : ¬ SourceConjecture := by
  intro h
  exact finite_trajectory (h w0 seed_squarefree (by rw [seed_potential]; decide))
#print axioms source_refutation
end Nonchalant
'''
(D/'lean/Nonchalant.lean').write_text(s)
