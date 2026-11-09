module
public import URMatchingDirectedCycle
@[expose] public section
namespace URMatching
universe u
variable {I : Type u}

/-- A genuine finite directed walk, with a total indexing function only to avoid
irrelevant out-of-range choices. All n consecutive arcs are required. -/
def DirectedWalkCertificate (R : I → I → Prop) (a b : I) (n : ℕ) (f : ℕ → I) : Prop :=
  0 < n ∧ f 0 = a ∧ f n = b ∧ ∀ k, k < n → R (f k) (f (k+1))

theorem transGen_walk_certificate {R : I → I → Prop} {a b : I}
    (h : Relation.TransGen R a b) :
    ∃ n f, DirectedWalkCertificate R a b n f := by
  classical
  induction h with
  | @single b hab =>
    refine ⟨1, (fun k => if k = 0 then a else b), by decide, by simp, by simp, ?_⟩
    intro k hk
    have : k = 0 := by omega
    subst k
    simpa using hab
  | @tail b c hab hbc ih =>
    obtain ⟨n, f, hn, hf0, hfn, hf⟩ := ih
    let g : ℕ → I := fun k => if k ≤ n then f k else c
    refine ⟨n+1, g, by omega, ?_, ?_, ?_⟩
    · simpa [g] using hf0
    · simp [g]
    · intro k hk
      by_cases hkn : k < n
      · simpa [g, Nat.le_of_lt hkn, show k+1 ≤ n by omega] using hf k hkn
      · have : k = n := by omega
        subst k
        simpa [g, hfn] using hbc

/-- Every closed directed walk in a loopless relation contains an actual simple
cycle. Shortest-walk minimization removes all repetitions, with no enumeration. -/
theorem transGen_cycle_list [DecidableEq I] {R : I → I → Prop}
    (loopless : ∀ i, ¬ R i i) {a : I} (h : Relation.TransGen R a a) :
    ∃ l, DirectedCycleList R l := by
  classical
  have hex : ∃ n : ℕ, ∃ (f : ℕ → I), 0 < n ∧ f 0 = f n ∧
      ∀ k, k < n → R (f k) (f (k+1)) := by
    obtain ⟨n, f, hn, h0, hlast, hf⟩ := transGen_walk_certificate h
    exact ⟨n, f, hn, h0.trans hlast.symm, hf⟩
  let n := Nat.find hex
  obtain ⟨f, hn, hclose, hf⟩ := Nat.find_spec hex
  have hmin : ∀ m < n, ¬ ∃ (g : ℕ → I), 0 < m ∧ g 0 = g m ∧
      ∀ k, k < m → R (g k) (g (k+1)) := by
    intro m hm
    exact Nat.find_min hex hm
  have htwo : 2 ≤ n := by
    by_contra hc
    have he : n = 1 := by omega
    have harc := hf 0 hn
    rw [show 0+1 = n by omega, ← hclose] at harc
    exact loopless _ harc
  have hinj : Function.Injective (fun i : Fin n => f i.val) := by
    intro i j hij
    have forbid : ∀ i j : Fin n, i.val < j.val → f i.val = f j.val → False := by
      intro i j hlt he
      apply hmin (j.val-i.val) (by omega)
      refine ⟨fun k => f (i.val+k), by omega, ?_, ?_⟩
      · simpa [Nat.add_sub_of_le (Nat.le_of_lt hlt)] using he
      · intro k hk
        simpa [Nat.add_assoc] using hf (i.val+k) (by omega)
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact forbid i j hlt hij
    · exact forbid j i hgt hij.symm
  let l := List.ofFn (fun i : Fin n => f i.val)
  refine ⟨l, ?_, ?_, ?_⟩
  · exact List.nodup_ofFn.mpr hinj
  · simpa [l] using htwo
  · intro k hk
    have hkn : k < n := by simpa [l] using hk
    have hn0 : 0 < n := hn
    simp only [l, List.length_ofFn, List.getElem_ofFn]
    change R (f k) (f ((k+1)%n))
    by_cases hs : k+1 < n
    · rw [Nat.mod_eq_of_lt hs]
      exact hf k hkn
    · have he : k+1 = n := by omega
      rw [he, Nat.mod_self, hclose]
      change R (f k) (f n)
      rw [← he]
      exact hf k hkn
end URMatching
