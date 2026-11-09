import SignedQuotient
namespace Nut8
variable {V : Type} [Fintype V] {m : ℕ} [NeZero m]

/-- Pull the actual graph back through the global labelling. -/
def coordinateGraph (G : SimpleGraph V) (L : Fin 8 × ZMod m ≃ V) :
    SimpleGraph (Fin 8 × ZMod m) where
  Adj p q := G.Adj (L p) (L q)
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun p => G.loopless.irrefl (L p)⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (L : Fin 8 × ZMod m ≃ V) :
    DecidableRel (coordinateGraph G L).Adj := fun p q => (inferInstance : Decidable (G.Adj (L p) (L q)))

lemma coordinateGraph_adjacency (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Fin 8 × ZMod m ≃ V) (u : V → ℝ) (p : Fin 8 × ZMod m) :
    adjacency (coordinateGraph G L) (u ∘ L) p = adjacency G u (L p) := by
  change (∑ q, (if G.Adj (L p) (L q) then 1 else 0) * u (L q)) =
    ∑ w, (if G.Adj (L p) w then 1 else 0) * u w
  exact Equiv.sum_comp L (fun w => (if G.Adj (L p) w then (1 : ℝ) else 0) * u w)

omit [Fintype V] in
lemma coordinateGraph_translation (G : SimpleGraph V)
    (σ : G ≃g G) (L : Fin 8 × ZMod m ≃ V)
    (hL : ∀ i a, L (i,a+1) = σ (L (i,a))) :
    TranslationInvariant (coordinateGraph G L) := by
  have step (i j : Fin 8) (a b : ZMod m) :
      G.Adj (L (i,a+1)) (L (j,b+1)) ↔ G.Adj (L (i,a)) (L (j,b)) := by
    rw [hL, hL, σ.map_adj_iff]
  have iter (n : ℕ) (i j : Fin 8) (a b : ZMod m) :
      G.Adj (L (i,a+n)) (L (j,b+n)) ↔ G.Adj (L (i,a)) (L (j,b)) := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
        (step i j (a+n) (b+n)).trans ih
  intro i j a b
  change G.Adj (L (i,a)) (L (j,b)) ↔ G.Adj (L (i,0)) (L (j,b-a))
  have h := iter (-a).val i j a b
  simpa only [ZMod.natCast_zmod_val, add_neg_cancel, ← sub_eq_add_neg] using h.symm

omit [Fintype V] in
lemma character_formula_of_step (σ : Equiv.Perm V)
    (L : Fin 8 × ZMod m ≃ V)
    (hL : ∀ i a, L (i,a+1) = σ (L (i,a)))
    (u : V → ℝ) (e : ℝ) (hu : ∀ v, u (σ v) = e * u v) :
    ∀ i b, u (L (i,b)) = e ^ b.val * u (L (i,0)) := by
  have iter (i : Fin 8) (n : ℕ) :
      u (L (i,(n : ZMod m))) = e ^ n * u (L (i,0)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, hL, hu, ih, pow_succ']
      ring
  intro i b
  simpa only [ZMod.natCast_zmod_val] using iter i b.val

/-- The sign is integral and periodic; the negative case retains its parity. -/
theorem nut_coordinate_character [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Nut G)
    (σ : G ≃g G) (hp : (σ.toEquiv : Equiv.Perm V) ^ m = 1)
    (L : Fin 8 × ZMod m ≃ V) (hL : ∀ i a, L (i,a+1) = σ (L (i,a))) :
    ∃ (u : V → ℝ) (ε : ℤ), adjacency G u = 0 ∧ (∀ v, u v ≠ 0) ∧
      (ε = 1 ∨ ε = -1 ∧ Even m) ∧ ε ^ m = 1 ∧
      ∀ i b, u (L (i,b)) = (character m ε b : ℝ) * u (L (i,0)) := by
  obtain ⟨u, e, _, hk, hf, hs, he⟩ := nut_sign_character G hn σ m (NeZero.ne m) hp
  have hpow (e : ℝ) (h : ∀ v, u (σ v) = e * u v) : e ^ m = 1 := by
    let T := pullback σ.toEquiv
    have ht : T u = e • u := by ext v; exact h v
    have hper : (T ^ m) u = u := by ext v; rw [pullback_pow, hp]; rfl
    have hnon : u ≠ 0 := by
      intro hz
      exact hf (L (0,0)) (congrFun hz _)
    exact (smul_left_injective ℝ hnon) (by
      change e ^ m • u = (1 : ℝ) • u
      rw [← iterate_scalar T u e ht m, hper, one_smul])
  rcases he with he | ⟨he, hm⟩
  · refine ⟨u, 1, hk, hf, Or.inl rfl, by simp, ?_⟩
    intro i b
    simpa [character, he] using character_formula_of_step σ.toEquiv L hL u _ hs i b
  · refine ⟨u, -1, hk, hf, Or.inr ⟨rfl, hm⟩, ?_, ?_⟩
    · exact_mod_cast (show (-1 : ℝ) ^ m = 1 by simpa only [he] using hpow _ hs)
    · intro i b
      simpa [character, he] using character_formula_of_step σ.toEquiv L hL u _ hs i b
end Nut8
