import Certificates
namespace Rainbow
open SimpleGraph
theorem valid0 : Valid G color0 := valid_of_certs cut0 side0 cert0
theorem valid1 : Valid Gᶜ color1 := valid_of_certs cut1 side1 cert1
theorem bound0 : rvd G ≤ 4 := csInf_le (OrderBot.bddBelow _) ⟨color0,valid0⟩
theorem bound1 : rvd Gᶜ ≤ 3 := csInf_le (OrderBot.bddBelow _) ⟨color1,valid1⟩
theorem connected0 : G.Connected := by
  suffices hr : ∀ v, G.Reachable 0 v from ⟨fun x y => (hr x).symm.trans (hr y)⟩
  intro v
  fin_cases v
  · exact Reachable.refl 0
  · exact (show G.Adj 0 1 by decide).reachable
  · exact (show G.Adj 0 3 by decide).reachable.trans (show G.Adj 3 2 by decide).reachable
  · exact (show G.Adj 0 3 by decide).reachable
  · exact (show G.Adj 0 3 by decide).reachable.trans (show G.Adj 3 4 by decide).reachable
  · exact (show G.Adj 0 1 by decide).reachable.trans (show G.Adj 1 5 by decide).reachable
  · exact (show G.Adj 0 6 by decide).reachable
  · exact (show G.Adj 0 7 by decide).reachable
theorem connected1 : Gᶜ.Connected := by
  suffices hr : ∀ v, Gᶜ.Reachable 0 v from ⟨fun x y => (hr x).symm.trans (hr y)⟩
  intro v
  fin_cases v
  · exact Reachable.refl 0
  · exact (show Gᶜ.Adj 0 2 by decide).reachable.trans (show Gᶜ.Adj 2 1 by decide).reachable
  · exact (show Gᶜ.Adj 0 2 by decide).reachable
  · exact (show Gᶜ.Adj 0 5 by decide).reachable.trans (show Gᶜ.Adj 5 3 by decide).reachable
  · exact (show Gᶜ.Adj 0 4 by decide).reachable
  · exact (show Gᶜ.Adj 0 5 by decide).reachable
  · exact (show Gᶜ.Adj 0 5 by decide).reachable.trans (show Gᶜ.Adj 5 6 by decide).reachable
  · exact (show Gᶜ.Adj 0 5 by decide).reachable.trans (show Gᶜ.Adj 5 7 by decide).reachable
theorem counterexample : G.Connected ∧ Gᶜ.Connected ∧ rvd G + rvd Gᶜ < 8 :=
  ⟨connected0,connected1, by have := bound0; have := bound1; omega⟩
theorem mathdb_346167 :
    ¬ (∀ (n : Nat) (H : SimpleGraph (Fin n)), 8 ≤ n →
      H.Connected → Hᶜ.Connected → n ≤ rvd H + rvd Hᶜ) := by
  intro h
  have bad := h 8 G (by decide) connected0 connected1
  have good := counterexample.2.2
  omega
end Rainbow
#print axioms Rainbow.mathdb_346167
