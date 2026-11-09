import Sigma.DartDeficit
import Mathlib.Data.Fintype.Prod

namespace Sigma365710
open Finset

def dartGood {V : Type*} (G : SimpleGraph V) (t : V × V × V) : Prop :=
  G.Adj t.1 t.2.1 ∧ ¬ G.Adj t.1 t.2.2 ∧ ¬ G.Adj t.2.1 t.2.2

instance {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (dartGood G) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def tripleSupport {V : Type*} [DecidableEq V] (t : V × V × V) : Finset V :=
  {t.1, t.2.1, t.2.2}

def swapDart {V : Type*} (t : V × V × V) : V × V × V := (t.2.1, t.1, t.2.2)

theorem dartGood_swap {V : Type*} (G : SimpleGraph V) {t : V × V × V}
    (h : dartGood G t) : dartGood G (swapDart t) :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

theorem support_swap {V : Type*} [DecidableEq V] (t : V × V × V) :
    tripleSupport (swapDart t) = tripleSupport t := by
  ext x
  simp only [tripleSupport, swapDart, mem_insert, mem_singleton]
  tauto

theorem card_dartGood {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (Fintype.card {t : Fin n × Fin n × Fin n // dartGood G t} : ℤ) = orderedDefect G := by
  classical
  rw [Fintype.card_subtype]
  rw [← Finset.sum_boole]
  simp only [Fintype.sum_prod_type, dartGood]
  unfold orderedDefect
  apply sum_congr rfl; intro u _
  apply sum_congr rfl; intro v _
  by_cases h : G.Adj u v <;> simp [h]

theorem deficit_ge_of_support_injection {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ht : G.CliqueFree 3) {ι : Type*} [Fintype ι]
    (f : ι → Fin n × Fin n × Fin n) (hf : ∀ i, dartGood G (f i))
    (hi : Function.Injective (fun i => tripleSupport (f i))) :
    (Fintype.card ι : ℤ) ≤ deficit G := by
  classical
  let lift : Bool × ι → {t : Fin n × Fin n × Fin n // dartGood G t} :=
    fun bi => if bi.1 then ⟨swapDart (f bi.2), dartGood_swap G (hf bi.2)⟩
      else ⟨f bi.2, hf bi.2⟩
  have hl : Function.Injective lift := by
    rintro ⟨b, i⟩ ⟨c, j⟩ he
    have hv := congrArg Subtype.val he
    have hs := congrArg tripleSupport hv
    have hij : i = j := by
      apply hi
      cases b <;> cases c <;> simpa [lift, support_swap] using hs
    subst j
    have hn := (hf i).1.ne
    cases b <;> cases c <;> simp_all [lift, swapDart, Prod.ext_iff]
  have hcard := Fintype.card_le_of_injective lift hl
  have hz : (Fintype.card (Bool × ι) : ℤ) ≤
      (Fintype.card {t : Fin n × Fin n × Fin n // dartGood G t} : ℤ) := by
    exact_mod_cast hcard
  rw [card_dartGood, orderedDefect_eq_twice_deficit G ht] at hz
  simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] at hz
  omega

end Sigma365710
