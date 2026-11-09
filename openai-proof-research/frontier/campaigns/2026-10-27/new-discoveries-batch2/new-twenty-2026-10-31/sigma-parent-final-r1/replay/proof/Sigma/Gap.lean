import Sigma.ConfigurationCount
import Sigma.Structure

namespace Sigma365710
open Finset

theorem oneEdgeTriple_dart {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {x y z : V} (h : OneEdgeTriple G x y z) :
    ∃ t : V × V × V, dartGood G t ∧ tripleSupport t = {x, y, z} := by
  rcases h.2.2.2 with h | h | h
  · exact ⟨(x,y,z), h, rfl⟩
  · refine ⟨(x,z,y), ⟨h.2.1, h.1, fun a => h.2.2 a.symm⟩, ?_⟩
    ext; simp [tripleSupport]; tauto
  · refine ⟨(y,z,x), ⟨h.2.2, fun a => h.1 a.symm, fun a => h.2.1 a.symm⟩, ?_⟩
    ext; simp [tripleSupport]; tauto

theorem inducedP4_deficit_gap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) {a b c d : Fin n} (hp : InducedP4 G a b c d) :
    (n : ℤ) - 2 ≤ deficit G := by
  classical
  rcases hp with ⟨habn,hacn,hadn,hbcn,hbdn,hcdn,hab,hbc,hcd,hac,had,hbd⟩
  let P : Finset (Fin n) := {a,b,c,d}
  let X := {x : Fin n // x ∉ P}
  have witness : ∀ x : X, ∃ t : Fin n × Fin n × Fin n,
      dartGood G t ∧ x.val ∈ tripleSupport t ∧ tripleSupport t ⊆ insert x.val P := by
    intro x
    have hx : x.val ≠ a ∧ x.val ≠ b ∧ x.val ≠ c ∧ x.val ≠ d := by
      have := x.property
      simpa [P, not_or] using this
    have hw := path_extension_witness G ht hab hbc hcd had hadn hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
    rcases hw with h | h | h | h
    all_goals
      obtain ⟨t, hg, hs⟩ := oneEdgeTriple_dart G h
      refine ⟨t,hg,?_,?_⟩
      · rw [hs]; simp
      · rw [hs]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢
        rcases hz with hz | hz | hz <;> subst z <;> simp [P]
  choose f hf using witness
  let selected : Bool ⊕ X → Fin n × Fin n × Fin n := fun i =>
    match i with
    | Sum.inl false => (a,b,d)
    | Sum.inl true => (c,d,a)
    | Sum.inr x => f x
  have good : ∀ i, dartGood G (selected i) := by
    rintro (i | x)
    · cases i
      · exact ⟨hab,had,hbd⟩
      · exact ⟨hcd,fun h => hac h.symm,fun h => had h.symm⟩
    · exact (hf x).1
  have seedsub : ∀ i : Bool, tripleSupport (selected (.inl i)) ⊆ P := by
    intro i; cases i <;> intro z hz <;> simp only [selected,tripleSupport,P,mem_insert,mem_singleton] at hz ⊢ <;> tauto
  have inj : Function.Injective (fun i => tripleSupport (selected i)) := by
    rintro (i | x) (j | y) he
    all_goals dsimp only at he
    · have bc : b ∉ ({c,d,a} : Finset (Fin n)) := by
        simp only [mem_insert, mem_singleton, not_or]; exact ⟨hbcn,hbdn,habn.symm⟩
      have bm : b ∈ ({a,b,d} : Finset (Fin n)) := by simp
      cases i <;> cases j
      · rfl
      · change ({a,b,d} : Finset (Fin n)) = {c,d,a} at he
        rw [he] at bm
        exact False.elim (bc bm)
      · change ({c,d,a} : Finset (Fin n)) = {a,b,d} at he
        rw [← he] at bm
        exact False.elim (bc bm)
      · rfl
    · have hy : y.val ∈ tripleSupport (selected (.inr y)) := (hf y).2.1
      rw [← he] at hy
      exact False.elim (y.property (seedsub i hy))
    · have hx : x.val ∈ tripleSupport (selected (.inr x)) := (hf x).2.1
      rw [he] at hx
      exact False.elim (x.property (seedsub j hx))
    · have hx := (hf x).2.1
      change x.val ∈ tripleSupport (selected (.inr x)) at hx
      rw [he] at hx
      have hm := (hf y).2.2 hx
      have hxy : x = y := by
        apply Subtype.ext
        exact (mem_insert.mp hm).resolve_right x.property
      subst y; rfl
  have bound := deficit_ge_of_support_injection G ht selected good inj
  have pc : P.card = 4 := by simp [P,habn,hacn,hadn,hbcn,hbdn,hcdn]
  have xc : Fintype.card X = n - 4 := by
    change Fintype.card {x : Fin n // x ∉ P} = n - 4
    rw [Fintype.card_subtype_compl]
    have hpc : Fintype.card {x : Fin n // x ∈ P} = 4 := by
      simpa using pc
    simp only [Fintype.card_fin, hpc]
  have hn : 4 ≤ n := by
    have h := card_le_card (subset_univ P)
    simpa [pc] using h
  simp only [Fintype.card_sum, Fintype.card_bool, xc, Nat.cast_add, Nat.cast_ofNat] at bound
  rw [Nat.cast_sub hn] at bound
  omega

theorem non_completeBipartition_deficit_gap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hc : G.Connected) (ht : G.CliqueFree 3)
    (hb : ¬ HasCompleteBipartition G) : (n : ℤ) - 2 ≤ deficit G := by
  obtain ⟨a,b,c,d,hp⟩ := inducedP4_of_not_completeBipartition G hc ht hb
  exact inducedP4_deficit_gap G ht hp

end Sigma365710
