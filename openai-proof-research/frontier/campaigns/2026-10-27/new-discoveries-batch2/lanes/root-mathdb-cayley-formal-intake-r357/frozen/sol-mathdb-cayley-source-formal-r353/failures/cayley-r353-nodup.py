from pathlib import Path
p=Path('Definitions.lean');s=p.read_text();i=s.index('theorem le_maxL');s=s[:i]+'''theorem nodup_allWords (n m : ℕ) : (allWords n m).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a _
      exact ih.map (by intro u v h; exact List.cons.inj h |>.2)
    · apply List.nodup_range.pairwise.imp
      intro a b hab
      apply List.disjoint_left.mpr
      intro u hu hv
      obtain ⟨v, _, he⟩ := List.mem_map.mp hu
      obtain ⟨z, _, he'⟩ := List.mem_map.mp hv
      have := List.cons.inj (he.trans he'.symm) |>.1
      exact hab (by omega)

'''+s[i:];i=s.index('/-- Source count');s=s[:i]+'''def avoiderList (n : ℕ) (p : List ℕ) : List (List ℕ) :=
  (allWords n n).filter (fun w => packedB w && !(containsB p w))
theorem card_eq_length (n : ℕ) (p : List ℕ) :
    (avoiders n p).card = (avoiderList n p).length := by
  have he : avoiders n p = (avoiderList n p).toFinset := by
    ext w
    simp only [avoiders, wordUniverse, avoiderList, Finset.mem_filter,
      List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    tauto
  rw [he]
  exact List.toFinset_card_of_nodup ((nodup_allWords n n).filter _)

'''+s[i:];p.write_text(s)
