from pathlib import Path
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r1')
p=root/'src/Definitions.lean'; s=p.read_text(); mark='\ndef Subset'
s=s.replace(mark,'''  quadrangle : ∃ a b c d : Points q,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ∀ l, card [a,b,c,d] (fun p => inc p l) ≤ 2
'''+mark)
pos=s.index('def Conjecture20')
s=s[:pos]+'''theorem time_unique {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (hp : Percolates P r a) (t : Nat) (ht : TimeIs P r a t) : time P r a hp = t := by
  have hl := time_is_least P r a hp
  have h1 : ¬ time P r a hp < t := fun h => ht.2 _ h hl.1
  have h2 : ¬ t < time P r a hp := fun h => hl.2 _ h ht.1
  omega

theorem step_of_full {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Full a) : step P r a = a := by
  funext p
  simp [step, h p]

theorem percolates_iff_full_stable {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) :
    Percolates P r a ↔ ∃ n, Full (rounds P r a n) ∧
      rounds P r a n = rounds P r a (n+1) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn, (step_of_full P r _ hn).symm⟩
  · rintro ⟨n, hn, _⟩
    exact ⟨n, hn⟩
''' +s[pos:];p.write_text(s)
p=root/'src/Plane5.lean';s=p.read_text().replace('  meet := pg_meet','  meet := pg_meet\n  quadrangle := ⟨0,25,30,6, by decide⟩');p.write_text(s)
