from pathlib import Path
p=Path(__file__).resolve().parent.parent/'src/GridOrbitPaths.lean'
s=p.read_text().replace('using congrArg (· = 1) hd','using Iff.of_eq (congrArg (· = 1) hd)')
s=s.replace('      exact saturated_neighbor_preimage hr (fun a b hab => ih a b hab) h','      simpa only [and_comm] using saturated_neighbor_preimage hr (fun a b hab => ih a b hab) h')
s=s.replace('      change m-1-u.1.val = v.1.val','      simp only [rowFlip, Equiv.prodCongr_apply, Prod.map_fst, Fin.revPerm_apply, Fin.val_rev]')
s=s.replace('have ev : v = (⟨m-1,by omega⟩,0) := Prod.ext (Fin.ext (by omega)) (Subsingleton.elim _ _)','have vv : v.1.val = m-1 := by omega\n        have ev : v = (⟨m-1,by omega⟩,0) := Prod.ext (Fin.ext vv) (Subsingleton.elim _ _)')
s=s.replace('have ev : v = (⟨0,by omega⟩,0) := Prod.ext (Fin.ext (by omega)) (Subsingleton.elim _ _)','have vv : v.1.val = 0 := by omega\n        have ev : v = (⟨0,by omega⟩,0) := Prod.ext (Fin.ext vv) (Subsingleton.elim _ _)')
s=s.replace('        rw [eu,ev] at huv\n        exact r.symm huv','        simpa only [eu,ev] using r.symm huv').replace('        rw [eu,ev] at huv\n        exact huv','        simpa only [eu,ev] using huv').replace('dif_neg hm1','dite_eq_right hm1')
s=s.replace('      apply congrArg (fun i : Fin m => r (i,0) (⟨0,h0⟩,0))\n      apply Fin.ext\n      change m-1-0 = m-1\n      omega','      apply Prod.ext\n      · apply Fin.ext\n        simp [rowFlip, Fin.val_rev]\n      · exact Subsingleton.elim _ _')
p.write_text(s)
