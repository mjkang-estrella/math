import Transport
import RawWye
namespace Transport
open Literal
set_option linter.unusedSimpArgs false
noncomputable def representedGraph {rows g} (rep : Represents rows g) : Literal.Graph where
  order := rows.length
  edge i j := g.edge (rep.choose i) (rep.choose j)
  symm _ _ := g.symm _ _
  loopless _ := g.loopless _

 theorem canonical_step {rows g h} (rep : Represents rows g) (move : YYDelta g h) :
    ∃ x, x ∈ Delta153.verts rows ∧ Delta153.wye rows x = true ∧
      Represents (Delta153.reduce rows x) h := by
  let r := representedGraph rep
  have he (i j : Fin rows.length) : Delta153.edge rows i.val j.val = r.edge i j :=
    rep.choose_spec i j
  have mr : YYDelta r h := relabel_move rep.choose (by intros; rfl) move
  obtain ⟨x,a,b,c,keep,hn,hi,hs,hab,hac,hbc,hax,hbx,hcx,hr,hm⟩ := mr
  change Fin rows.length at x a b c
  change Fin h.order → Fin rows.length at keep
  have row (v : Fin rows.length) : Delta153.edge rows x.val v.val =
      if v = a ∨ v = b ∨ v = c then 2 else 0 := (he x v).trans (hr v)
  refine ⟨x.val, List.mem_range.mpr x.isLt, RawIndex.wye_of_row rows x a b c hab hac hbc row, ?_⟩
  let ke : Fin h.order ≃ {v : Fin rows.length // v ≠ x} :=
    Equiv.ofBijective (fun i => ⟨keep i, (hs (keep i)).mpr ⟨i,rfl⟩⟩)
      ⟨fun _ _ hh => hi (congrArg Subtype.val hh), by
        intro v
        obtain ⟨i,hh⟩ := (hs v.val).mp v.property
        exact ⟨i, Subtype.ext hh⟩⟩
  let se := RawIndex.survivorEquiv rows x
  let e : Fin (Delta153.reduce rows x.val).length ≃ Fin h.order :=
    (finCongr (RawIndex.reduce_length rows x.val)).trans (se.trans ke.symm)
  refine ⟨e, ?_⟩
  intro i j
  let ii := (finCongr (RawIndex.reduce_length rows x.val)) i
  let jj := (finCongr (RawIndex.reduce_length rows x.val)) j
  have ki : keep (e i) = RawIndex.old rows x.val ii := by
    have hh := congrArg Subtype.val (ke.apply_symm_apply (se ii))
    exact hh
  have kj : keep (e j) = RawIndex.old rows x.val jj := by
    have hh := congrArg Subtype.val (ke.apply_symm_apply (se jj))
    exact hh
  have neq : (e i ≠ e j) ↔ RawIndex.old rows x.val ii ≠ RawIndex.old rows x.val jj := by
    rw [← ki, ← kj]
    exact hi.ne_iff.symm
  change Delta153.edge (Delta153.reduce rows x.val) ii.val jj.val = _
  rw [RawIndex.reduce_edge, hm, ki, kj, he]
  congr 1
  have ri := row (RawIndex.old rows x.val ii)
  have rj := row (RawIndex.old rows x.val jj)
  simp only [bne_iff_ne, beq_iff_eq, Bool.and_eq_true, Fin.val_inj] at *
  rw [ri, rj]
  simp only [ite_eq_left_iff, OfNat.ofNat_ne_zero, imp_false] at *
  split_ifs <;> simp_all only [Fin.ext_iff] <;> grind

 theorem canonical_transport {k} (path : Literal.Pure Concrete.g0 k) :
    ∃ rows, RawClosure.Pure Delta153.original rows ∧ rows.length = k.order := by
  obtain ⟨rows, hp, hr⟩ := pure_transport (@canonical_step) original_represents path
  exact ⟨rows, hp, represented_order hr⟩
#print axioms canonical_transport
end Transport
