from pathlib import Path
D=Path(__file__).resolve().parents[1]
def vv(x,y):return f'({x},{y})'
rows=[]
for S in range(3):
 for x in range(3):
  for y in range(36):
   path=[(z,0) for z in (range(S+1,x+1) if x>=S else range(S-1,x-1,-1))]+[(x,z) for z in range(1,y+1)]
   rows.append('['+','.join(vv(*v) for v in path)+']')
s='\ndef spineCertificates : Fin 324 → List (Vertex 3 36) := ![\n'+',\n'.join(rows)+']\n'
s+='''def spineCert (S : Fin 3) (v : Vertex 3 36) :=
 spineCertificates ⟨S.val*108+v.1.val*36+v.2.val, by omega⟩
theorem spine_certificate_valid : ∀ (S : Fin 3) (v : Vertex 3 36),
 checkPath (S,0) (spineCert S v) v = true ∧
 (spineCert S v).length = potential S v := by decide
 theorem spine_walk_iff (S : Fin 3) (v : Vertex 3 36) (r : ℕ) :
 (∃ p : (graph 3 36).Walk (S,0) v, p.length ≤ r) ↔ potential S v ≤ r := by
 constructor
 · rintro ⟨p,hp⟩
   have hh := potential_walk S p
   have hz : potential S (S, (0 : Fin 36)) = 0 := by simp [potential, Nat.dist]
   omega
 · intro hr
   obtain ⟨p,hp⟩ := path_sound _ _ _ (spine_certificate_valid S v).1
   exact ⟨p,by simpa [hp, (spine_certificate_valid S v).2] using hr⟩
noncomputable def actualResidual (n m T : ℕ) (S : Fin n) (hm : 0<m) : List ℕ := by
 classical
 exact List.ofFn fun x : Fin n =>
  ((Finset.univ : Finset (Fin m)).filter fun y =>
   ¬ ∃ p : (graph n m).Walk (S,⟨0,hm⟩) (x,y), p.length ≤ T-1).card
 def ActualGreedySuccess (n m T : ℕ) (S : Fin n) (hm : 0<m) : Prop :=
 0<T ∧ n≤T ∧ (finish (T-1) (actualResidual n m T S hm)).all (· == 0) = true
 theorem actual_residual_eq (S : Fin 3) (T : Fin 11) (hT : 3≤T.val) :
 actualResidual 3 36 T.val S (by decide) = residual 3 36 T.val S.val := by
 unfold actualResidual
 simp only [spine_walk_iff]
 have h : ∀ (S : Fin 3) (T : Fin 11), 3≤T.val →
   (List.ofFn fun x : Fin 3 => ((Finset.univ : Finset (Fin 36)).filter
    fun y => ¬ potential S (x,y) ≤ T.val-1).card) = residual 3 36 T.val S.val := by decide
 exact h S T hT
 theorem actual_greedy_failure : ∀ (S : Fin 3) (T : Fin 11),
 ¬ ActualGreedySuccess 3 36 T.val S (by decide) := by
 intro S T h
 have hh := h.2.1
 have eq := actual_residual_eq S T hh
 have hf : GreedySuccess 3 36 T.val S.val :=
  ⟨h.1,hh,S.isLt,by simpa [eq] using h.2.2⟩
 exact greedy_fails_through_ten S T hf
-- Literal universal optimality assertion for tooth-dominant combs, in minimum-free form.
def LiteralConjecture : Prop := ∀ n m (hn : 0<n) (hnm : n≤m), ∀ T,
 Burnable n m T → ∃ S : Fin n, ∃ t, t≤T ∧ ActualGreedySuccess n m t S (lt_of_lt_of_le hn hnm)
theorem literal_source_refutation : ¬ LiteralConjecture := by
 intro h
 obtain ⟨S,t,ht,hg⟩ := h 3 36 (by decide) (by decide) 10 burnable_ten
 exact actual_greedy_failure S ⟨t,by omega⟩ hg
'''
s=s.replace('\n theorem','\ntheorem').replace('\n def Actual','\ndef Actual')
p=D/'formal/Comb.lean';t=p.read_text();t=t[:t.index('end Comb373367')]+s+'\nend Comb373367\n#print axioms Comb373367.literal_source_refutation\n';p.write_text(t)
