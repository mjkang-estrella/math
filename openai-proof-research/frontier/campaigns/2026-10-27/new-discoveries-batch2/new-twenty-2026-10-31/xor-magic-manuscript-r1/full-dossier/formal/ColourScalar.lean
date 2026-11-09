import ColourOrientation
import LiftMagicBridge
set_option linter.unusedSimpArgs false
namespace XorMagic
variable {m d : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
variable {F : MatchingDecomposition G d} {hd : 2 ≤ d} (b : FactorColouring F hd)

omit [DecidableRel G.Adj] in
theorem directed_mate (u : Fin m) (i : Fin d) :
    b.directed u (F.mate i u) =
      if i = ⟨0, by omega⟩ then (if b.colour u then 1 else 2)
      else if i = ⟨1, by omega⟩ then (if b.colour u then 2 else 1) else 0 := by
  simp only [FactorColouring.directed, (F.distinct u).eq_iff, eq_comm]

theorem scalar_colour_identity : ∀ (z : Bool) (x : Four),
    scalar (if z then 1 else 2) x + scalar (if z then 2 else 1) x = x := by decide

theorem scalar_colour_sum (u : Fin m) (x : Four) :
    (∑ v ∈ G.neighborFinset u, scalar (outgoingSlope G (chosenSlopes G b) u v) x) =
    d • x + x := by
  classical
  have hb : (∑ v ∈ G.neighborFinset u, scalar (outgoingSlope G (chosenSlopes G b) u v) x) =
      ∑ i : Fin d, scalar (b.directed u (F.mate i u)) x := by
    symm
    apply Finset.sum_bij (fun i _ => F.mate i u)
    · intro i _; simpa using (F.cover _ _).mpr ⟨i,rfl⟩
    · intro i _ j _ h; exact F.distinct u h
    · intro v hv; obtain ⟨i,hi⟩ := (F.cover _ _).mp (by simpa using hv)
      exact ⟨i,Finset.mem_univ _,hi⟩
    · intro i _
      rw [chosen_outgoing G b ((F.cover _ _).mpr ⟨i,rfl⟩)]
  rw [hb]
  let a : Four := scalar (if b.colour u then 1 else 2) x
  let c : Four := scalar (if b.colour u then 2 else 1) x
  have hx : ∀ y : Four, y+y=0 := by decide
  have ht (i : Fin d) : scalar (b.directed u (F.mate i u)) x =
      x + (if i = ⟨0, by omega⟩ then a+x else 0) +
        (if i = ⟨1, by omega⟩ then c+x else 0) := by
    have hn : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
      intro hh; have hval := congrArg Fin.val hh; simp at hval
    rw [directed_mate]
    by_cases h0 : i = ⟨0, by omega⟩
    · have h1 : i ≠ ⟨1, by omega⟩ := by intro h; have hh := congrArg Fin.val (h0.symm.trans h); simp at hh
      simp only [h0, hn, ite_true, ite_false, add_zero]
      change a = x+(a+x)
      calc
        _ = a+(x+x) := by rw [hx,add_zero]
        _ = _ := by abel
    · by_cases h1 : i = ⟨1, by omega⟩
      · simp only [h1, Ne.symm hn, ite_false, ite_true, add_zero, zero_add]
        change c = x+(c+x)
        calc
          _ = c+(x+x) := by rw [hx,add_zero]
          _ = _ := by abel
      · simp [h0,h1,scalar]
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have hac : a+c=x := scalar_colour_identity _ _
  calc
    _ = d • x + (a+c) + (x+x) := by abel
    _ = _ := by rw [hac,hx,add_zero]

theorem chosen_open_scalar (h : Odd d) (u : Fin m) (x : Four) :
    (∑ v ∈ G.neighborFinset u, scalar (outgoingSlope G (chosenSlopes G b) u v) x) = 0 := by
  rw [scalar_colour_sum]
  obtain ⟨k,hk⟩ := h
  rw [hk,add_nsmul,show 2*k=k+k by omega,add_nsmul,one_nsmul]
  have hx : ∀ y : Four, y+y=0 := by decide
  simp [add_assoc, hx]

theorem chosen_closed_scalar (h : Even d) (u : Fin m) (x : Four) :
    x + (∑ v ∈ G.neighborFinset u, scalar (outgoingSlope G (chosenSlopes G b) u v) x) = 0 := by
  rw [scalar_colour_sum]
  obtain ⟨k,hk⟩ := h
  rw [hk,add_nsmul]
  have hx : ∀ y : Four, y+y=0 := by decide
  simp [hx]
end XorMagic
