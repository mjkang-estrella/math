import Definitions
import Mathlib.Data.Nat.Bitwise
namespace EdgePattern.MaskR3
open scoped BigOperators

def decode (n m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => m.testBit i = true)

theorem complete {n : ℕ} (s : Finset (Fin n)) :
    ∃ m < 2^n, decode n m = s := by
  let bs := List.ofFn (fun i : Fin n => decide (i ∈ s))
  let b := BitVec.ofBoolListLE bs
  refine ⟨b.toNat, ?_, ?_⟩
  · simpa [b, bs] using b.isLt
  · ext i
    simp only [decode, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
    simp [bs, List.getD_eq_getElem?_getD]

theorem decode_inj {n a b : ℕ} (ha : a < 2^n) (hb : b < 2^n)
    (h : decode n a = decode n b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have he := Finset.ext_iff.mp h ⟨i,hi⟩
    simp only [decode, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Bool.eq_iff_iff.mpr he
  · rw [Nat.testBit_eq_false_of_lt, Nat.testBit_eq_false_of_lt]
    · exact hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    · exact ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

def ok {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) : Prop :=
  ∀ i : Fin n, ∀ j : Fin n, m.testBit i = true → m.testBit j = true → ¬ G.Adj i j
instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) : Decidable (ok G m) :=
  inferInstanceAs (Decidable (∀ i : Fin n, ∀ j : Fin n,
    m.testBit i = true → m.testBit j = true → ¬ G.Adj i j))

theorem ok_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ) :
    ok G m ↔ Independent G (decode n m) := by
  simp only [ok, Independent, decode, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h v hv w hw
    exact h v w hv hw
  · intro h v w hv hw
    exact h v hv w hw

def candidates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.range (2^n)).filter (ok G)
def size (n m : ℕ) : ℕ := (decode n m).card
def largest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  (candidates G).sup (size n)
def best {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset ℕ :=
  (candidates G).filter (fun m => size n m = largest G)

theorem best_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) : m ∈ best G ↔ m < 2^n ∧ Maximum G (decode n m) := by
  simp only [best, candidates, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hm,ho⟩,hs⟩
    refine ⟨hm, (ok_iff G m).mp ho, ?_⟩
    intro t ht
    obtain ⟨k,hk,rfl⟩ := complete t
    change size n k ≤ size n m
    rw [hs]
    exact Finset.le_sup (f := size n) (by simp [candidates, hk, (ok_iff G k).mpr ht])
  · rintro ⟨hm,ho,hs⟩
    have hok := (ok_iff G m).mpr ho
    refine ⟨⟨hm,hok⟩, le_antisymm ?_ ?_⟩
    · exact Finset.le_sup (f := size n) (by simp [candidates,hm,hok])
    · apply Finset.sup_le
      intro k hk
      have hki : ok G k := (Finset.mem_filter.mp hk).2
      exact hs _ ((ok_iff G k).mp hki)

theorem maxima_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    maxima G = (best G).image (decode n) := by
  classical
  ext s
  simp only [maxima, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hs
    obtain ⟨m,hm,rfl⟩ := complete s
    exact ⟨m,(best_iff G m).mpr ⟨hm,hs⟩,rfl⟩
  · rintro ⟨m,hm,rfl⟩
    exact ((best_iff G m).mp hm).2

def blockCheck {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : ℕ) (ms : Finset ℕ) (lo len : ℕ) : Prop :=
  ∀ i : Fin len, ok G (lo + i.val) →
    size n (lo + i.val) ≤ M ∧ (size n (lo + i.val) = M → lo + i.val ∈ ms)
instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : ℕ) (ms : Finset ℕ) (lo len : ℕ) : Decidable (blockCheck G M ms lo len) :=
  inferInstanceAs (Decidable (∀ i : Fin len, ok G (lo + i.val) →
    size n (lo + i.val) ≤ M ∧ (size n (lo + i.val) = M → lo + i.val ∈ ms)))

theorem best_of_checks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : ℕ) (ms : Finset ℕ) (hne : ms.Nonempty)
    (listed : ∀ m ∈ ms, m < 2^n ∧ ok G m ∧ size n m = M)
    (all : ∀ m < 2^n, ok G m → size n m ≤ M ∧ (size n m = M → m ∈ ms)) :
    best G = ms := by
  ext m
  constructor
  · intro hm
    obtain ⟨hm,hind,hmax⟩ := (best_iff G m).mp hm
    have hi := (ok_iff G m).mpr hind
    have hmle := (all m hm hi).1
    obtain ⟨k,hk⟩ := hne
    have hl := listed k hk
    have hmge : M ≤ size n m := hl.2.2 ▸ hmax _ ((ok_iff G k).mp hl.2.1)
    exact (all m hm hi).2 (le_antisymm hmle hmge)
  · intro hm
    have hl := listed m hm
    apply (best_iff G m).mpr
    refine ⟨hl.1, (ok_iff G m).mp hl.2.1, ?_⟩
    intro t ht
    obtain ⟨k,hk,rfl⟩ := complete t
    change size n k ≤ size n m
    rw [hl.2.2]
    exact (all k hk ((ok_iff G k).mpr ht)).1
end EdgePattern.MaskR3
