import CycLower
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort

/-!
# Upper bound: every 2-colouring of `K_N`, `N = (a-1)(b-2)+1`, contains a colour-1 cyclic `S_a`
or a colour-2 cyclic `P_b^{mon}`.

Theorem A (new): if `t ≥ 1`, `b ≥ 4`, `N = (t+1)(b-2)+1` and every vertex has at most `t`
non-blue (colour-code `0`) partners, then there is a blue clockwise path on `b` vertices.
-/

namespace CycRamsey

/-- residue map `ℕ → Fin N` -/
def fm (N : ℕ) (hN : 0 < N) (x : ℕ) : Fin N := ⟨x % N, Nat.mod_lt _ hN⟩

theorem fm_add_self (N : ℕ) (hN : 0 < N) (x : ℕ) : fm N hN (x + N) = fm N hN x := by
  apply Fin.ext; simp [fm]

theorem fm_mod (N : ℕ) (hN : 0 < N) (x : ℕ) : fm N hN (x % N) = fm N hN x := by
  apply Fin.ext; simp [fm]

theorem fm_mod_add (N : ℕ) (hN : 0 < N) (x d : ℕ) : fm N hN (x % N + d) = fm N hN (x + d) := by
  apply Fin.ext; simp [fm, Nat.mod_add_mod]

theorem fin2_ne_one {z : Fin 2} (h : z ≠ 1) : z = 0 := by
  apply Fin.ext; have := z.isLt; have : z.val ≠ 1 := fun e => h (Fin.ext e); simp; omega

/-- A path from an increasing sequence of positions with span `< N`. -/
theorem path_of_positions {N b : ℕ} (hN : 0 < N) (hb : 0 < b) (c : Colouring N) (q : ℕ → ℕ)
    (hinc : ∀ i, i + 1 < b → q i < q (i + 1)) (hspan : q (b - 1) < q 0 + N)
    (hblue : ∀ i, i + 1 < b → c s(fm N hN (q i), fm N hN (q (i + 1))) = 1) :
    ContainsCyc (monPath b) c 1 := by
  have hlt : ∀ i j, i < j → j < b → q i < q j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_or_ge i j with h | h
      · exact lt_trans (ih h (by omega)) (hinc j hj)
      · have : i = j := by omega
        subst this; exact hinc i hj
  have hle : ∀ i, i < b → q i ≤ q (b - 1) := by
    intro i hi
    rcases Nat.lt_or_ge i (b - 1) with h | h
    · exact le_of_lt (hlt i (b - 1) h (by omega))
    · have : i = b - 1 := by omega
      rw [this]
  let Q : Fin b → ℕ := fun i => q i.val
  have hQ : StrictMono Q := fun i j hij => hlt i.val j.val hij j.isLt
  have hspan' : ∀ i : Fin b, Q i < Q ⟨0, hb⟩ + N := by
    intro i; exact lt_of_le_of_lt (hle i.val i.isLt) hspan
  refine ⟨fun i => (⟨Q i % N, Nat.mod_lt _ hN⟩ : Fin N), rot_embedding hN hb Q hQ hspan', ?_⟩
  intro u v huv
  rw [monPath, SimpleGraph.fromRel_adj] at huv
  rcases huv.2 with h | h
  · have := hblue u.val (by omega)
    rw [h] at this; exact this
  · have := hblue v.val (by omega)
    rw [h, Sym2.eq_swap] at this; exact this

section TheoremA

variable {N t b : ℕ} (hN : 0 < N) (c : Colouring N)

/-- blue relation on positions -/
def Bl (x y : ℕ) : Prop := c s(fm N hN x, fm N hN y) = 1

/-- the set of non-blue offsets of `v` -/
def nonBlue (v : ℕ) : Finset ℕ :=
  (Finset.Ico 1 N).filter (fun d => c s(fm N hN v, fm N hN (v + d)) = 0)

theorem theoremA (hNdef : N = (t + 1) * (b - 2) + 1) (ht : 1 ≤ t) (hb : 4 ≤ b)
    (hdeg : ∀ v, (nonBlue hN c v).card ≤ t) (hno : ¬ ContainsCyc (monPath b) c 1) : False := by
  classical
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 4 := ⟨b - 4, by omega⟩
  set P := b' * (t + 1) with hP
  have hNP : N = P + 2 * (t + 1) + 1 := by
    rw [hNdef, hP]; simp only [show b' + 4 - 2 = b' + 2 by omega]; ring
  have hNt : 2 * t + 3 ≤ N := by omega
  -- basic facts on the blue relation
  have hsym : ∀ x y, Bl hN c x y ↔ Bl hN c y x := by
    intro x y; unfold Bl; rw [Sym2.eq_swap]
  have hmodB : ∀ x d, Bl hN c (x % N) (x % N + d) ↔ Bl hN c x (x + d) := by
    intro x d; unfold Bl; rw [fm_mod, fm_mod_add]
  have hnb : ∀ x d, d ∈ Finset.Ico 1 N → ¬ Bl hN c x (x + d) → d ∈ nonBlue hN c x := by
    intro x d hd h
    unfold nonBlue; rw [Finset.mem_filter]
    exact ⟨hd, fin2_ne_one h⟩
  -- forward jump
  have hJex : ∀ y, ∃ j, 1 ≤ j ∧ j ≤ t + 1 ∧ Bl hN c y (y + j) := by
    intro y
    by_contra hcon
    push Not at hcon
    have hsub : Finset.Ico 1 (t + 2) ⊆ nonBlue hN c y := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      exact hnb y d (by rw [Finset.mem_Ico]; omega) (hcon d hd.1 (by omega))
    have := Finset.card_le_card hsub
    have h2 := hdeg y
    rw [Nat.card_Ico] at this
    omega
  -- backward jump
  have hKex : ∀ y, ∃ k, 1 ≤ k ∧ k ≤ t + 1 ∧ Bl hN c y (y + (N - k)) := by
    intro y
    by_contra hcon
    push Not at hcon
    have hsub : Finset.Ico (N - (t + 1)) N ⊆ nonBlue hN c y := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      have := hcon (N - d) (by omega) (by omega)
      rw [show N - (N - d) = d by omega] at this
      exact hnb y d (by rw [Finset.mem_Ico]; omega) this
    have := Finset.card_le_card hsub
    have h2 := hdeg y
    rw [Nat.card_Ico] at this
    omega
  let J : ℕ → ℕ := fun x => Nat.find (hJex (x % N))
  let K : ℕ → ℕ := fun x => Nat.find (hKex (x % N))
  have hJspec : ∀ x, 1 ≤ J x ∧ J x ≤ t + 1 ∧ Bl hN c x (x + J x) := by
    intro x
    have h := Nat.find_spec (hJex (x % N))
    exact ⟨h.1, h.2.1, (hmodB x _).mp h.2.2⟩
  have hJmin : ∀ x j, 1 ≤ j → j < J x → ¬ Bl hN c x (x + j) := by
    intro x j h1 hj hB
    have := Nat.find_min (hJex (x % N)) hj
    apply this
    have hJ := (hJspec x).2.1
    exact ⟨h1, by omega, (hmodB x j).mpr hB⟩
  have hKspec : ∀ x, 1 ≤ K x ∧ K x ≤ t + 1 ∧ Bl hN c x (x + (N - K x)) := by
    intro x
    have h := Nat.find_spec (hKex (x % N))
    exact ⟨h.1, h.2.1, (hmodB x _).mp h.2.2⟩
  have hKmin : ∀ x k, 1 ≤ k → k < K x → ¬ Bl hN c x (x + (N - k)) := by
    intro x k h1 hk hB
    have := Nat.find_min (hKex (x % N)) hk
    apply this
    have hK := (hKspec x).2.1
    exact ⟨h1, by omega, (hmodB x _).mpr hB⟩
  have hJper : ∀ x, J (x + N) = J x := by
    intro x
    show Nat.find (hJex ((x + N) % N)) = Nat.find (hJex (x % N))
    simp only [Nat.add_mod_right]
  -- (F3) J + K ≤ t + 2
  have hJK : ∀ x, J x + K x ≤ t + 2 := by
    intro x
    obtain ⟨hJ1, hJt, -⟩ := hJspec x
    obtain ⟨hK1, hKt, -⟩ := hKspec x
    have hsub : Finset.Ico 1 (J x) ∪ Finset.Ico (N + 1 - K x) N ⊆ nonBlue hN c x := by
      intro d hd
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at hd
      rcases hd with hd | hd
      · exact hnb x d (by rw [Finset.mem_Ico]; omega) (hJmin x d hd.1 hd.2)
      · have := hKmin x (N - d) (by omega) (by omega)
        rw [show N - (N - d) = d by omega] at this
        exact hnb x d (by rw [Finset.mem_Ico]; omega) this
    have hdisj : Disjoint (Finset.Ico 1 (J x)) (Finset.Ico (N + 1 - K x) N) := by
      rw [Finset.disjoint_left]
      intro d h1 h2
      rw [Finset.mem_Ico] at h1 h2
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Nat.card_Ico] at this
    have h2 := hdeg x
    omega
  -- greedy orbit
  let orb : ℕ → ℕ → ℕ := fun s n => Nat.rec s (fun _ y => y + J y) n
  have horb0 : ∀ s, orb s 0 = s := fun s => rfl
  have horbS : ∀ s n, orb s (n + 1) = orb s n + J (orb s n) := fun s n => rfl
  have horb_le : ∀ s n, orb s n ≤ s + n * (t + 1) := by
    intro s n
    induction n with
    | zero => simp [horb0]
    | succ n ih =>
      rw [horbS]; have := (hJspec (orb s n)).2.1
      rw [Nat.add_mul, one_mul]; omega
  -- (F4/F5): J (x + J x) = t + 1 for every x
  have hL5 : ∀ x, J (x + J x) = t + 1 := by
    intro x
    by_contra hne
    have hJt := (hJspec (x + J x)).2.1
    have hsmall : J (x + J x) ≤ t := by omega
    let q : ℕ → ℕ := fun i => if i = 0 then x + N - K x else orb (x + N) (i - 1)
    have hq0 : q 0 = x + N - K x := rfl
    have hqS : ∀ i, q (i + 1) = orb (x + N) i := fun i => by simp [q]
    apply hno
    refine path_of_positions hN (by omega) c q ?_ ?_ ?_
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; rw [hq0, hqS, horb0]; have := (hKspec x).1; omega
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [hqS, hqS, horbS]; have := (hJspec (orb (x + N) i')).1; omega
    · -- span estimate
      have e1 : orb (x + N) 1 = x + N + J x := by
        have h := horbS (x + N) 0
        rw [horb0, Nat.zero_add] at h
        rw [h, hJper]
      have e2 : J (orb (x + N) 1) = J (x + J x) := by
        rw [e1, show x + N + J x = (x + J x) + N by ring, hJper]
      have e3 : orb (x + N) 2 ≤ x + N + J x + t := by
        have h := horbS (x + N) 1
        show orb (x + N) (1 + 1) ≤ _
        rw [h, e2, e1]; omega
      have e4 : ∀ n, orb (x + N) (n + 2) ≤ orb (x + N) 2 + n * (t + 1) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have h := horbS (x + N) (n + 2)
          rw [show n + 2 + 1 = n + 1 + 2 by omega] at h
          rw [h]
          have := (hJspec (orb (x + N) (n + 2))).2.1
          rw [Nat.add_mul, one_mul]; omega
      have hb1 : b' + 4 - 1 = (b' + 2) + 1 := by omega
      rw [hb1, hqS, hq0]
      have := e4 b'
      have hK := (hKspec x).2.1
      have hJK' := hJK x
      have : b' * (t + 1) = P := rfl
      omega
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        rw [hq0, hqS, horb0]
        have hK := hKspec x
        have hb := hK.2.2
        unfold Bl at hb
        rw [show x + N - K x = x + (N - K x) by omega, fm_add_self, Sym2.eq_swap]
        exact hb
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [hqS, hqS, horbS]
        exact (hJspec _).2.2
  -- orbit of `u = J 0` moves by exactly `t + 1`
  have horbit : ∀ k, J (J 0 + k * (t + 1)) = t + 1 := by
    intro k
    induction k with
    | zero => simpa using hL5 0
    | succ k ih =>
      have := hL5 (J 0 + k * (t + 1))
      rw [ih] at this
      rw [Nat.add_mul, one_mul, ← Nat.add_assoc]; exact this
  have hy := horbit (b' + 2)
  have hy' : J 0 + (b' + 2) * (t + 1) = J 0 + (N - 1) := by
    have : (b' + 2) * (t + 1) = P + 2 * (t + 1) := by rw [hP]; ring
    omega
  rw [hy'] at hy
  have hnot := hJmin (J 0 + (N - 1)) 1 le_rfl (by omega)
  have hK0 : K (J 0) = 1 := by
    have h1 := hJK (J 0)
    have h2 := horbit 0
    simp at h2
    have := (hKspec (J 0)).1
    omega
  have hblue := (hKspec (J 0)).2.2
  rw [hK0] at hblue
  apply hnot
  unfold Bl at hblue ⊢
  rw [show J 0 + (N - 1) + 1 = J 0 + N by omega, fm_add_self, Sym2.eq_swap]
  exact hblue

end TheoremA

end CycRamsey
