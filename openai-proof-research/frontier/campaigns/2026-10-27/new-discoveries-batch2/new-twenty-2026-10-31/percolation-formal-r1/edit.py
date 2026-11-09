from pathlib import Path
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r1')
p=root/'src/Definitions.lean'
s=p.read_text(); start=s.index('noncomputable def time'); end=s.index('def Conjecture20',start)
s=s[:start]+'''theorem exists_time {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r a) : ∃ t, TimeIs P r a t := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : ∃ k, k < n ∧ Full (rounds P r a k)
    · obtain ⟨k, hk, hf⟩ := he
      exact ih k hk hf
    · exact ⟨n, hn, fun k hk hf => he ⟨k, hk, hf⟩⟩
noncomputable def time {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r a) : Nat := Classical.choose (exists_time P r a h)
theorem time_is_least {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r a) : TimeIs P r a (time P r a h) :=
  Classical.choose_spec (exists_time P r a h)
''' +s[end:]
s=s.replace('    by_contra h\n','    apply Classical.byContradiction\n    intro h\n')
p.write_text(s)
