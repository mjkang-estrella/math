import SemWords
namespace ChanLevine
variable {n : ℕ}

theorem LegalWord.trace {c d : SignedConfig n} {w} (h : LegalWord c w d) :
    ∃ (f : ℕ → SignedConfig n) (a : ℕ → ZMod n),
      f 0 = c ∧ f w.length = d ∧
      (∀ t, t < w.length → 0 < (f t).x (a t) ∧ f (t+1) = fire (f t) (a t)) ∧
      (∀ k ∈ w, ∃ t, t < w.length ∧ a t = k) := by
  induction h with
  | nil c => exact ⟨fun _ => c, fun _ => 0, rfl, rfl, by simp, by simp⟩
  | @cons c d w v hv hw ih =>
    obtain ⟨f, a, hf, hd, hs, hm⟩ := ih
    refine ⟨(fun t => if t = 0 then c else f (t-1)),
      (fun t => if t = 0 then v else a (t-1)), by simp, ?_, ?_, ?_⟩
    · simpa using hd
    · intro t ht
      cases t with
      | zero => simpa [hf] using And.intro hv hf
      | succ t => simpa using hs t (by simpa using ht)
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨t, ht, ha⟩ := hm k hk
        exact ⟨t+1, by simpa using ht, by simpa using ha⟩

/-- A closed legal word covering every vertex repeats to a diverse forward walk. -/
theorem closed_word_diverse {c : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w c) (hw : w ≠ []) (hcover : ∀ k, k ∈ w) :
    DiverseWalkIn (component c) := by
  obtain ⟨f, a, hzero, hend, hstep, hmem⟩ := h.trace
  have hpos : 0 < w.length := List.length_pos_iff.mpr hw
  have hr : ∀ t, t ≤ w.length → Reach c (f t) := by
    intro t ht
    induction t with
    | zero => rw [hzero]
    | succ t ih =>
      have hs := hstep t (by omega)
      exact (ih (by omega)).tail ⟨a t, hs.1, hs.2⟩
  refine ⟨fun t => f (t % w.length), fun t => a (t % w.length), ?_, ?_, ?_⟩
  · intro t
    exact ⟨f (t % w.length), hr _ (Nat.le_of_lt (Nat.mod_lt _ hpos)), .refl⟩
  · intro t
    have ht := Nat.mod_lt t hpos
    have hs := hstep (t % w.length) ht
    refine ⟨hs.1, ?_⟩
    have he : (t+1) % w.length = (t % w.length + 1) % w.length := by
      conv_lhs => rw [Nat.add_mod]
      conv_rhs => rw [Nat.add_mod]
      simp
    change f ((t+1) % w.length) = fire (f (t % w.length)) (a (t % w.length))
    rw [he]
    by_cases hb : t % w.length + 1 < w.length
    · rw [Nat.mod_eq_of_lt hb]
      exact hs.2
    · have he' : t % w.length + 1 = w.length := by omega
      rw [he', Nat.mod_self, hzero]
      rw [he', hend] at hs
      exact hs.2
  · intro v T
    obtain ⟨t, ht, ha⟩ := hmem v (hcover v)
    refine ⟨(T+1)*w.length + t, ?_, ?_⟩
    · nlinarith
    · simpa [Nat.add_mod, Nat.mod_eq_of_lt ht] using ha

theorem ambientBridge_of_coverage (h : ClosedCoverage) : AmbientBridge := by
  intro n inst hn
  refine ⟨recurrent_nonnegative_of_coverage h n hn, ?_⟩
  intro c hc
  obtain ⟨w, hw, hl⟩ := recurrent_closed_word hc
  exact ⟨⟨c, rfl⟩, Or.inl (closed_word_diverse hl hw (h n hn c w hw hl))⟩
end ChanLevine
