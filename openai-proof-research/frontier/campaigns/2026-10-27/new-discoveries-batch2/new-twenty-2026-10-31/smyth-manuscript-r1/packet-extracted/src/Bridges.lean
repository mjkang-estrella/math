import Base
namespace Smyth1512
theorem gens_length : ∀ g ∈ gens, g.length = 5 := by decide

/-! ## Enumerator lemmas -/

theorem mem_comps : ∀ (m n : ℕ) (l : List ℕ), l ∈ comps m n ↔ l.length = m ∧ l.sum = n := by
  intro m
  induction m with
  | zero =>
    intro n l
    cases l with
    | nil => simp [comps, eq_comm]
    | cons x xs => simp [comps]
  | succ m ih =>
    intro n l
    cases l with
    | nil => simp [comps]
    | cons x xs =>
      simp only [comps, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq,
        List.length_cons, List.sum_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨i, hi, ys, hys, rfl, rfl⟩
        change ys ∈ comps m (n-i) at hys
        rw [ih] at hys
        exact ⟨hys.1, by omega⟩
      · rintro ⟨hlen, hsum⟩
        exact ⟨x, by omega, xs, (ih _ _).2 ⟨hlen, by omega⟩, rfl, rfl⟩

theorem nodup_comps : ∀ (m n : ℕ), (comps m n).Nodup := by
  intro m
  induction m with
  | zero => intro n; by_cases h : n = 0 <;> simp [comps, h]
  | succ m ih =>
    intro n
    simp only [comps]
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => (ih _).map (fun a b h => List.cons_injective h), ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := n + 1))
    intro i j _ _ hij
    change List.Disjoint ((comps m (n - i)).map (List.cons i)) ((comps m (n - j)).map (List.cons j))
    rw [List.disjoint_left]
    intro l hl hl'
    simp only [List.mem_map] at hl hl'
    obtain ⟨_, _, rfl⟩ := hl
    obtain ⟨_, _, h⟩ := hl'
    exact hij (List.cons.inj h).1.symm

theorem SL_nodup : SL.Nodup :=
  ((nodup_comps 3 19).product (nodup_comps 2 20)).filter _

/-! ## Dominance lemmas -/

theorem DomL.trans {l₁ l₂ l₃ : List ℕ} (h₁ : DomL l₁ l₂) (h₂ : DomL l₂ l₃) : DomL l₁ l₃ :=
  ⟨h₁.1.trans h₂.1, fun j => (h₂.2 j).trans (h₁.2 j)⟩

theorem psum_of_ge {l : List ℕ} {j : ℕ} (h : l.length ≤ j) : psum l j = l.sum := by
  simp [psum, List.take_of_length_le h]

theorem domB_iff {g l : List ℕ} (hg : g.length = 5) (hl : l.length = 5) :
    domB g l = true ↔ DomL g l := by
  unfold domB DomL
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hj⟩
    refine ⟨hs, fun j => ?_⟩
    by_cases hj5 : j < 6
    · exact hj j hj5
    · rw [psum_of_ge (by omega), psum_of_ge (by omega)]; exact hs ▸ le_rfl
  · rintro ⟨hs, hj⟩
    exact ⟨hs, fun j _ => hj j⟩

theorem length_sortL (l : List ℕ) : (sortL l).length = l.length :=
  List.length_insertionSort _ _

theorem inDB_mono {l l' : List ℕ} (hl : l.length = 5) (hl' : l'.length = 5)
    (h : inDB l = true) (hd : DomL l l') : inDB l' = true := by
  unfold inDB at *
  rw [List.any_eq_true] at *
  obtain ⟨g, hg, hgl⟩ := h
  refine ⟨g, hg, ?_⟩
  have h5 := gens_length g hg
  exact (domB_iff h5 hl').2 (((domB_iff h5 hl).1 hgl).trans hd)

theorem rearr_concat {A B : ℕ} (f : Fin A → ℕ) (g : Fin B → ℕ) :
    rearr (concat f g) = sortL (List.ofFn f ++ List.ofFn g) := by
  simp [rearr, sortL, concat, List.ofFn_fin_append]

/-! ## Realisation of enumerated lists as compositions -/

def toFun (k : ℕ) (l : List ℕ) : Fin k → ℕ := fun i => l.getD i 0

theorem ofFn_toFun {k : ℕ} {l : List ℕ} (h : l.length = k) : List.ofFn (toFun k l) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [toFun, List.getElem?_eq_getElem h2]

theorem sum_toFun {k : ℕ} {l : List ℕ} (h : l.length = k) : ∑ i, toFun k l i = l.sum := by
  rw [← List.sum_ofFn, ofFn_toFun h]

end Smyth1512
