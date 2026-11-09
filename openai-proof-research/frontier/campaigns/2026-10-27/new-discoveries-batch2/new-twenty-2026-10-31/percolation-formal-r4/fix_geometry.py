from pathlib import Path
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4');S=R/'packet/src'
p=S/'Noncollinear.lean';text=p.read_text();text='\n'.join(x for x in text.splitlines() if not x.startswith('import Geometry'))+'\n'
a=text.index('theorem line_fixed5');b=text.index('theorem line_nonfull5')
text=text[:a]+'''theorem line_fixed5 (l p : Points 5) :
    step PG5 5 (fun x => incidence x l) p = incidence p l := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp only [step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with hp | ⟨k,_,hpk,hc⟩
    · exact hp
    · by_cases he : l = k
      · subst k; exact hpk
      · have hm := PG5.meet l k he
        change card (List.finRange 31) (fun x => incidence x l && incidence x k) = 1 at hm
        change 5 ≤ card (List.finRange 31) (fun x => incidence x l && incidence x k) at hc
        omega
  · intro hp
    simp only [step, Bool.or_eq_true]
    exact Or.inl hp

theorem join_unique5 (p q l k : Points 5) (hne : p ≠ q)
    (hpl : incidence p l = true) (hql : incidence q l = true)
    (hpk : incidence p k = true) (hqk : incidence q k = true) : l = k := by
  have h := PG5.join p q hne
  obtain ⟨x,hx⟩ := List.length_eq_one_iff.mp h
  have hl : l ∈ (List.finRange 31).filter (fun j => incidence p j && incidence q j) := by
    simp [hpl,hql]
  have hk : k ∈ (List.finRange 31).filter (fun j => incidence p j && incidence q j) := by
    simp [hpk,hqk]
  rw [hx] at hl hk
  exact (List.eq_of_mem_singleton hl).trans (List.eq_of_mem_singleton hk).symm

'''+text[b:]
p.write_text(text)
for p in S.glob('Geometry*.lean'):p.unlink()
