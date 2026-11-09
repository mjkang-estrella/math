import pathlib,json,hashlib,re
p=pathlib.Path('TorusPMD.lean');s=p.read_text();mark=' theorem pmd_le_five'
bridge='''-- The infimum really is the minimum on every graph admitting a decomposition.
theorem pmd_minimum {α : Type} {G : α → α → Prop} {k : ℕ}
    (h : Decomposition G k) :
    Decomposition G (pmd G) ∧ ∀ j, Decomposition G j → pmd G ≤ j := by
  exact ⟨Nat.sInf_mem ⟨k, h⟩, fun _ hj => Nat.sInf_le hj⟩
-- Each edge belongs to exactly one part of the coloring partition.
theorem parts_partition {α : Type} {G : α → α → Prop} {k : ℕ}
    (color : α → α → Fin k) (u v : α) :
    G u v ↔ ∃! i, G u v ∧ color u v = i := by
  constructor
  · intro h
    exact ⟨color u v, ⟨h, rfl⟩, fun _ hi => hi.2.symm⟩
  · rintro ⟨_, ⟨h, _⟩, _⟩
    exact h
-- Deleting earlier parts is exactly the residual-edge comparison used above.
theorem residual_partition {α : Type} {G : α → α → Prop} {k : ℕ}
    (color : α → α → Fin k) (i : Fin k) (u v : α) :
    (G u v ∧ ¬ ∃ j : Fin k, j.val < i.val ∧ G u v ∧ color u v = j) ↔
    (G u v ∧ i.val ≤ (color u v).val) := by
  constructor
  · rintro ⟨hG, hn⟩
    refine ⟨hG, ?_⟩
    by_contra h
    exact hn ⟨color u v, by omega, hG, rfl⟩
  · rintro ⟨hG, hi⟩
    refine ⟨hG, ?_⟩
    rintro ⟨j, hj, _, he⟩
    rw [← he] at hj
    omega
'''
s=s.replace(mark,bridge+mark);p.write_text(s)
# compact registry screen without dumping JSON lines.
r=json.load(open('outputs/registry-screen.json'));o=r['openai_cached_listing'];pp=pathlib.Path(o['path']);t=json.load(open(pp));paths=[x['path'] for x in t.get('tree',[])];o.pop('matching_text',None);o['paths']=len(paths);o['truncated']=t.get('truncated');o['hits']=[x for x in paths if re.search('shareshian|elementary.positivity|positive.match|dihedral|pseudoperiod',x,re.I)];json.dump(r,open('outputs/registry-screen.json','w'),indent=2)
print('OpenAI matching paths',o['hits'][:12]);print('Omega matching paths',r['omega-Problems.json']['hits'])
