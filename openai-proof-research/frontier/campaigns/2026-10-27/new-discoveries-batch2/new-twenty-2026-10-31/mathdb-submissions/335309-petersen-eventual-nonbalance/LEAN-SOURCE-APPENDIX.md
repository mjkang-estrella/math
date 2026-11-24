# Lean source appendix — stage 4

Complete source packet for Petersen.miklavic_sparl_4_4. Fresh compilation and independent kernel receipts are recorded in REPORT.md and VALIDATION.json.

### `PetersenDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace Petersen

/-- `false` labels u, `true` labels v. The relation is precisely source (1). -/
def GP (n k : ℕ) [NeZero n] : SimpleGraph (Bool × ZMod n) :=
  SimpleGraph.fromRel fun x y =>
    (x.1 = false ∧ y.1 = false ∧ y.2 = x.2 + 1) ∨
    (x.1 = true ∧ y.1 = true ∧ y.2 = x.2 + (k : ZMod n)) ∨
    (x.1 = false ∧ y.1 = true ∧ y.2 = x.2)

instance (n k : ℕ) [NeZero n] : DecidableRel (GP n k).Adj :=
  by unfold GP; infer_instance

def nk (k : ℕ) : ℕ :=
  if k = 2 then 11 else if Odd k then (k + 1)^2 else k * (k + 2)

theorem nk_pos (k : ℕ) (hk : 2 ≤ k) : 0 < nk k := by
  unfold nk
  split_ifs
  · omega
  · exact pow_pos (by omega) _
  · exact Nat.mul_pos (by omega) (by omega)

noncomputable def W {V : Type*} [Fintype V] (G : SimpleGraph V) (x y : V) : Finset V :=
  Finset.univ.filter (fun w => G.dist x w < G.dist y w)

def LDB {V : Type*} [Fintype V] (G : SimpleGraph V) (ell : ℕ) : Prop :=
  ∀ x y, G.dist x y = ell → (W G x y).card = (W G y x).card

/-- Literal three-conjunct endpoint required by the independent review. -/
def MiklavicSparl44 : Prop :=
  (∀ k (_hk : 2 ≤ k), ∀ n (hn : nk k < n),
    letI : NeZero n := ⟨by omega⟩
    (GP n k).Connected) ∧
  (∀ k (_hk : 2 ≤ k), ∀ n (hn : nk k < n),
    letI : NeZero n := ⟨by omega⟩
    ∀ ell, 1 ≤ ell → ell < (GP n k).diam → ¬ LDB (GP n k) ell) ∧
  (∀ k (hk : 2 ≤ k),
    letI : NeZero (nk k) := ⟨Nat.ne_of_gt (nk_pos k hk)⟩
    ∃ ell, 1 ≤ ell ∧ ell < (GP (nk k) k).diam ∧ LDB (GP (nk k) k) ell)

end Petersen
```

### `PetersenWalks.lean`

```lean
import PetersenDefinitions
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Petersen

variable {n k : ℕ} [NeZero n]

def step (k : ℕ) (b : Bool) : ZMod n := if b then k else 1

theorem layer_step (b : Bool) (i : ZMod n) :
    (b,i) = (b,i+step k b) ∨ (GP n k).Adj (b,i) (b,i+step k b) := by
  by_cases h : (b,i) = (b,i+step k b)
  · exact Or.inl h
  · right
    refine ⟨h, Or.inl ?_⟩
    cases b <;> simp [step]

theorem outer_step (i : ZMod n) :
    (false,i) = (false,i+1) ∨ (GP n k).Adj (false,i) (false,i+1) :=
  layer_step false i

theorem spoke (i : ZMod n) : (GP n k).Adj (false,i) (true,i) := by
  simp [GP]

theorem layer_nat_walk (b : Bool) (i : ZMod n) (m : ℕ) :
    ∃ w : (GP n k).Walk (b,i) (b,i+step k b*(m : ZMod n)), w.length ≤ m := by
  induction m with
  | zero =>
    exact ⟨SimpleGraph.Walk.nil.copy rfl (by simp), by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    have he : i+step k b*((m+1 : ℕ) : ZMod n) = (i+step k b*(m : ZMod n))+step k b := by
      simp [Nat.cast_add, mul_add, add_assoc]
    rw [he]
    rcases layer_step (k := k) b (i+step k b*(m : ZMod n)) with h | h
    · exact ⟨w.copy rfl h, by simpa using Nat.le_succ_of_le hw⟩
    · exact ⟨w.append h.toWalk, by simpa using Nat.add_le_add_right hw 1⟩

theorem layer_walk (b : Bool) (i : ZMod n) (z : ℤ) :
    ∃ w : (GP n k).Walk (b,i) (b,i+step k b*(z : ZMod n)), w.length ≤ z.natAbs := by
  cases z with
  | ofNat m =>
    change ∃ w : (GP n k).Walk (b,i) (b,i+step k b*((m : ℤ) : ZMod n)), w.length ≤ m
    rw [Int.cast_natCast]
    exact layer_nat_walk b i m
  | negSucc m =>
    obtain ⟨w, hw⟩ := layer_nat_walk (k := k) b
      (i+step k b*((Int.negSucc m : ℤ) : ZMod n)) (m+1)
    have he : i+step k b*((Int.negSucc m : ℤ) : ZMod n)+step k b*((m+1 : ℕ) : ZMod n) = i := by
      push_cast
      ring
    exact ⟨(w.copy rfl (congrArg (fun a => (b,a)) he)).reverse, by simpa using hw⟩

theorem outer_reachable (a b : ZMod n) : (GP n k).Reachable (false,a) (false,b) := by
  obtain ⟨w, _⟩ := layer_nat_walk (k := k) false a (b-a).val
  have he : a+step k false*((b-a).val : ZMod n) = b := by
    simp [step, ZMod.natCast_zmod_val]
  exact ⟨he ▸ w⟩

theorem gp_connected (n k : ℕ) [NeZero n] : (GP n k).Connected := by
  refine { preconnected := ?_ }
  rintro ⟨a,i⟩ ⟨b,j⟩
  have h := outer_reachable (k := k) i j
  cases a <;> cases b
  · exact h
  · exact h.trans (spoke j).reachable
  · exact (spoke i).symm.reachable.trans h
  · exact (spoke i).symm.reachable.trans (h.trans (spoke j).reachable)

#print axioms gp_connected
#print axioms layer_walk
end Petersen
```

### `PetersenSanity.lean`

```lean
import PetersenWalks

namespace Petersen

theorem petersen_card : Fintype.card (Bool × ZMod 5) = 10 := by decide

theorem petersen_cubic : ∀ x, (GP 5 2).degree x = 3 := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide

private theorem petersen_two_steps : ∀ x y : Bool × ZMod 5,
    x = y ∨ (GP 5 2).Adj x y ∨ ∃ z, (GP 5 2).Adj x z ∧ (GP 5 2).Adj z y := by
  decide

theorem petersen_diam : (GP 5 2).diam = 2 := by
  have hu : (GP 5 2).ediam ≤ 2 := by
    apply SimpleGraph.ediam_le_of_edist_le
    intro x y
    rcases petersen_two_steps x y with h | h | ⟨z, hx, hy⟩
    · subst y; simp
    · rw [SimpleGraph.edist_eq_one_iff_adj.mpr h]; decide
    · simpa using SimpleGraph.edist_le (hx.toWalk.append hy.toWalk)
  have hl : 2 ≤ (GP 5 2).ediam := by
    have he : (GP 5 2).edist (false,0) (false,2) = 2 := by
      apply SimpleGraph.edist_eq_two_iff.mpr
      exact ⟨by decide, by decide, ⟨(false,1), by decide⟩⟩
    rw [← he]
    exact SimpleGraph.edist_le_ediam
  unfold SimpleGraph.diam
  rw [le_antisymm hu hl]
  rfl

#print axioms petersen_card
#print axioms petersen_cubic
#print axioms petersen_diam
end Petersen
```

### `PetersenCounts.lean`

```lean
import PetersenWalks

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem walk_step_counts {x y : Bool × ZMod n} (w : (GP n k).Walk x y) :
  ∃ a b : ℤ, ∃ s : ℕ,
    y.2 = x.2 + (a : ZMod n) + (k : ZMod n)*(b : ZMod n) ∧
    a.natAbs + b.natAbs + s ≤ w.length ∧
    s % 2 = (if x.1 = y.1 then 0 else 1) ∧
    (s = 0 → (x.1 = false → b = 0) ∧ (x.1 = true → a = 0)) := by
  induction w with
  | nil => exact ⟨0,0,0, by simp⟩
  | @cons x y z h w ih =>
    obtain ⟨a,b,s,he,hl,hpar,hpure⟩ := ih
    rcases h.2 with h | h
    · rcases h with h | h | h
      · refine ⟨a+1,b,s,?_,?_,?_,?_⟩
        · rw [he, h.2.2]; push_cast; ring
        · have ha := Int.natAbs_add_le a 1
          simp only [Int.natAbs_one, SimpleGraph.Walk.length_cons] at *
          omega
        · simpa [h.1, h.2.1] using hpar
        · intro hs
          have ht := hpure hs
          simp_all
      · refine ⟨a,b+1,s,?_,?_,?_,?_⟩
        · rw [he, h.2.2]; push_cast; ring
        · have hb := Int.natAbs_add_le b 1
          simp only [Int.natAbs_one, SimpleGraph.Walk.length_cons] at *
          omega
        · simpa [h.1, h.2.1] using hpar
        · intro hs
          have ht := hpure hs
          simp_all
      · refine ⟨a,b,s+1,?_,by simp only [SimpleGraph.Walk.length_cons]; omega,?_,?_⟩
        · simpa [h.2.2] using he
        · cases hz : z.1 <;> simp_all <;> omega
        · omega
    · rcases h with h | h | h
      · refine ⟨a-1,b,s,?_,?_,?_,?_⟩
        · rw [he, h.2.2]; push_cast; ring
        · have ha := Int.natAbs_sub_le a 1
          simp only [Int.natAbs_one, SimpleGraph.Walk.length_cons] at *
          omega
        · simpa [h.1, h.2.1] using hpar
        · intro hs
          have ht := hpure hs
          simp_all
      · refine ⟨a,b-1,s,?_,?_,?_,?_⟩
        · rw [he, h.2.2]; push_cast; ring
        · have hb := Int.natAbs_sub_le b 1
          simp only [Int.natAbs_one, SimpleGraph.Walk.length_cons] at *
          omega
        · simpa [h.1, h.2.1] using hpar
        · intro hs
          have ht := hpure hs
          simp_all
      · refine ⟨a,b,s+1,?_,by simp only [SimpleGraph.Walk.length_cons]; omega,?_,?_⟩
        · simpa [h.2.2] using he
        · cases hz : z.1 <;> simp_all <;> omega
        · omega

#print axioms walk_step_counts
end Petersen
```

### `PetersenMetric.lean`

```lean
import PetersenCounts
import Mathlib.Tactic.Abel

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- Minimum number of ±1 and ±k steps in the cyclic index group. -/
noncomputable def word (n k : ℕ) [NeZero n] (j : ZMod n) : ℕ :=
  sInf {d : ℕ | ∃ a b : ℤ, (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j ∧
    a.natAbs+b.natAbs = d}

theorem word_exists (j : ZMod n) :
    ∃ a b : ℤ, (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j ∧
      a.natAbs+b.natAbs = word n k j := by
  unfold word
  exact Nat.sInf_mem (s := {d : ℕ | ∃ a b : ℤ, (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j ∧ a.natAbs+b.natAbs = d}) ⟨j.val, ⟨(j.val : ℤ),0,by simp,by simp only [Int.natAbs_natCast, Int.natAbs_zero, Nat.add_zero]⟩⟩

theorem word_le (j : ZMod n) (a b : ℤ)
    (h : (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j) :
    word n k j ≤ a.natAbs+b.natAbs :=
  Nat.sInf_le ⟨a,b,h,rfl⟩

/-- Pure-layer extended word length; ∞ means the inner residue is unreachable. -/
noncomputable def pure (n : ℕ) [NeZero n] (c j : ZMod n) : ℕ∞ :=
  ⨅ z : {z : ℤ // c*(z : ZMod n) = j}, (z.val.natAbs : ℕ∞)

theorem pure_le (c j : ZMod n) (z : ℤ) (h : c*(z : ZMod n) = j) :
    pure n c j ≤ (z.natAbs : ℕ∞) := by
  unfold pure
  exact iInf_le (fun z : {z : ℤ // c*(z : ZMod n) = j} => (z.val.natAbs : ℕ∞)) ⟨z,h⟩

theorem mixed_walk (i : ZMod n) (a b : ℤ) :
    ∃ w : (GP n k).Walk (false,i) (true,i+(a : ZMod n)+(k : ZMod n)*(b : ZMod n)),
      w.length ≤ a.natAbs+b.natAbs+1 := by
  obtain ⟨wa, ha⟩ : ∃ w : (GP n k).Walk (false,i) (false,i+(a : ZMod n)), w.length ≤ a.natAbs := by
    have h := layer_walk (k := k) false i a
    have hs : step (n := n) k false = 1 := rfl
    rw [hs, one_mul] at h
    exact h
  obtain ⟨wb, hb⟩ : ∃ w : (GP n k).Walk (true,i+(a : ZMod n))
      (true,i+(a : ZMod n)+(k : ZMod n)*(b : ZMod n)), w.length ≤ b.natAbs := by
    simpa [step] using layer_walk (k := k) true (i+(a : ZMod n)) b
  refine ⟨(wa.append (spoke (i+(a : ZMod n))).toWalk).append wb, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
  omega

theorem dist_mixed_word (i j : ZMod n) :
    (GP n k).dist (false,i) (true,j) = word n k (j-i)+1 := by
  apply Nat.le_antisymm
  · obtain ⟨a,b,he,hl⟩ := word_exists (k := k) (j-i)
    obtain ⟨w,hw⟩ := mixed_walk (k := k) i a b
    have hj : i+(a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j := by
      calc
        _ = i+((a : ZMod n)+(k : ZMod n)*(b : ZMod n)) := by abel
        _ = j := by rw [he]; abel
    have hd := SimpleGraph.dist_le (w.copy rfl (congrArg (fun t => (true,t)) hj))
    simp only [SimpleGraph.Walk.length_copy] at hd
    omega
  · obtain ⟨w,hw⟩ := (gp_connected n k).exists_walk_length_eq_dist (false,i) (true,j)
    obtain ⟨a,b,s,he,hl,hp,_⟩ := walk_step_counts w
    have hc : (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j-i := by
      dsimp at he
      rw [he]
      abel
    have hf := word_le (j-i) a b hc
    simp only [Bool.false_eq_true, ite_false] at hp
    omega

theorem dist_same_word (layer : Bool) (i j : ZMod n) :
    ((GP n k).dist (layer,i) (layer,j) : ℕ∞) =
      min (pure n (step k layer) (j-i)) ((word n k (j-i)+2 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · apply le_min
    · apply le_iInf
      intro z
      obtain ⟨w,hw⟩ := layer_walk (k := k) layer i z.val
      have he : i+step k layer*(z.val : ZMod n) = j := by rw [z.property]; abel
      have hd := SimpleGraph.dist_le (w.copy rfl (congrArg (fun t => (layer,t)) he))
      simp only [SimpleGraph.Walk.length_copy] at hd
      exact_mod_cast (hd.trans hw)
    · have hc := gp_connected n k
      have hs (a : ZMod n) : (GP n k).dist (false,a) (true,a) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr (spoke a)
      cases layer
      · have ht := hc.dist_triangle (u := (false,i)) (v := (true,j)) (w := (false,j))
        rw [dist_mixed_word, SimpleGraph.dist_comm (u := (true,j)), hs] at ht
        exact_mod_cast ht
      · have ht := hc.dist_triangle (u := (true,i)) (v := (false,i)) (w := (true,j))
        rw [SimpleGraph.dist_comm (u := (true,i)) (v := (false,i)), hs, dist_mixed_word] at ht
        exact_mod_cast (show (GP n k).dist (true,i) (true,j) ≤ word n k (j-i)+2 by omega)
  · obtain ⟨w,hw⟩ := (gp_connected n k).exists_walk_length_eq_dist (layer,i) (layer,j)
    obtain ⟨a,b,s,he,hl,hpar,hpure⟩ := walk_step_counts w
    have hc : (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j-i := by
      dsimp at he; rw [he]; abel
    by_cases hs : s = 0
    · have h0 := hpure hs
      cases layer
      · have hb : b = 0 := h0.1 rfl
        have hp : pure n (step k false) (j-i) ≤ (a.natAbs : ℕ∞) := by
          apply pure_le
          simpa [step, hb] using hc
        have hn : a.natAbs ≤ (GP n k).dist (false,i) (false,j) := by simp_all
        exact (min_le_left _ _).trans (hp.trans (by exact_mod_cast hn))
      · have ha : a = 0 := h0.2 rfl
        have hp : pure n (step k true) (j-i) ≤ (b.natAbs : ℕ∞) := by
          apply pure_le
          simpa [step, ha] using hc
        have hn : b.natAbs ≤ (GP n k).dist (true,i) (true,j) := by simp_all
        exact (min_le_left _ _).trans (hp.trans (by exact_mod_cast hn))
    · have hf := word_le (j-i) a b hc
      have h2 : 2 ≤ s := by simp only [ite_true] at hpar; omega
      have hn : word n k (j-i)+2 ≤ (GP n k).dist (layer,i) (layer,j) := by omega
      exact (min_le_right _ _).trans (by exact_mod_cast hn)

#print axioms dist_mixed_word
#print axioms dist_same_word
end Petersen
```

### `PetersenLine.lean`

```lean
import PetersenMetric
import Mathlib.Tactic.Linarith

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen

def H (k b : ℕ) : ℕ := min b (k+1-b)
def lineCost (k x : ℕ) : ℕ := x/k + H k (x%k)
def f (n k : ℕ) [NeZero n] (j : ZMod n) : ℕ :=
  min (lineCost k j.val) (lineCost k (n-j.val))
def p (n : ℕ) [NeZero n] (j : ZMod n) : ℕ := min j.val (n-j.val)
noncomputable def t (n k : ℕ) [NeZero n] (j : ZMod n) : ℕ∞ :=
  pure n (k : ZMod n) j

/-- The two nearest multiples of k minimize the integer line metric. -/
theorem line_lower (k q r a b : ℤ) (hk : 2 ≤ k) (_hr : 0 ≤ r) (_hrk : r < k)
    (he : a+k*b = q*k+r) :
    q+min r (k+1-r) ≤ |a|+|b| := by
  have hA := le_abs_self a
  have hB := le_abs_self b
  have hA' := neg_le_abs a
  by_cases hb : b ≤ q
  · have hm := min_le_left r (k+1-r)
    have hp := mul_nonneg (show 0 ≤ k-1 by omega) (show 0 ≤ q-b by omega)
    nlinarith
  · have hm := min_le_right r (k+1-r)
    have hp := mul_nonneg (show 0 ≤ k+1 by omega) (show 0 ≤ b-q-1 by omega)
    nlinarith

variable {k : ℕ}

theorem lineCost_cast (hk : 0 < k) (x : ℕ) :
    (lineCost k x : ℤ) = ((x/k : ℕ) : ℤ)+min ((x%k : ℕ) : ℤ) ((k : ℤ)+1-(x%k : ℕ)) := by
  have hr := Nat.mod_lt x hk
  simp only [lineCost, H, Nat.cast_add, Nat.cast_min, Nat.cast_sub (by omega : x%k ≤ k+1), Nat.cast_one]

theorem lineCost_min (hk : 2 ≤ k) (x : ℕ) :
  (∃ a b : ℤ, a+(k : ℤ)*b = x ∧ a.natAbs+b.natAbs = lineCost k x) ∧
  (∀ a b : ℤ, a+(k : ℤ)*b = x → lineCost k x ≤ a.natAbs+b.natAbs) := by
  have hk0 : 0 < k := by omega
  have hr := Nat.mod_lt x hk0
  have hd : (x : ℤ) = (x/k : ℕ)*(k : ℤ)+(x%k : ℕ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod x k).symm : x = x/k*k+x%k)
  have hc := lineCost_cast hk0 x
  constructor
  · by_cases h : ((x%k : ℕ) : ℤ) ≤ (k : ℤ)+1-(x%k : ℕ)
    · refine ⟨((x%k : ℕ) : ℤ), ((x/k : ℕ) : ℤ), ?_, ?_⟩
      · nlinarith
      · apply (Nat.cast_injective (R := ℤ))
        rw [Nat.cast_add, Int.natCast_natAbs, Int.natCast_natAbs, hc, min_eq_left h]
        rw [abs_of_nonneg (Int.natCast_nonneg _), abs_of_nonneg (Int.natCast_nonneg _)]
        ring
    · refine ⟨((x%k : ℕ) : ℤ)-(k : ℤ), ((x/k : ℕ) : ℤ)+1, ?_, ?_⟩
      · nlinarith
      · apply (Nat.cast_injective (R := ℤ))
        rw [Nat.cast_add, Int.natCast_natAbs, Int.natCast_natAbs, hc, min_eq_right (by omega)]
        rw [abs_of_nonpos (show ((x%k : ℕ) : ℤ)-(k : ℤ) ≤ 0 by omega),
          abs_of_nonneg (show 0 ≤ ((x/k : ℕ) : ℤ)+1 by have := Int.natCast_nonneg (x/k); omega)]
        ring
  · intro a b he
    have hl := line_lower (k : ℤ) (x/k : ℕ) (x%k : ℕ) a b (by omega) (by omega) (by omega) (he.trans hd)
    rw [← hc] at hl
    rw [← Int.natCast_natAbs, ← Int.natCast_natAbs, ← Nat.cast_add] at hl
    exact_mod_cast hl

#print axioms lineCost_min
end Petersen
```

### `PetersenCyclic.lean`

```lean
import PetersenLine

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem lineCost_upper (hk : 2 ≤ k) (x : ℕ) :
    2*(k : ℤ)*(lineCost k x : ℤ) ≤ 2*(x : ℤ)+(k : ℤ)*(k+1) := by
  have hc := lineCost_cast (by omega : 0 < k) x
  have hd : (x : ℤ) = (x/k : ℕ)*(k : ℤ)+(x%k : ℕ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod x k).symm : x = x/k*k+x%k)
  have h1 := min_le_left (((x%k : ℕ) : ℤ)) ((k : ℤ)+1-(x%k : ℕ))
  have h2 := min_le_right (((x%k : ℕ) : ℤ)) ((k : ℤ)+1-(x%k : ℕ))
  have hp := mul_nonneg (show 0 ≤ (k : ℤ) by omega)
    (show 0 ≤ (k : ℤ)+1-2*min (((x%k : ℕ) : ℤ)) ((k : ℤ)+1-(x%k : ℕ)) by omega)
  have hr : 0 ≤ ((x%k : ℕ) : ℤ) := Int.natCast_nonneg _
  nlinarith

theorem f_short (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) :
    (k : ℤ)*(f n k j : ℤ) < n := by
  have hj := j.val_lt
  have he : ((n-j.val : ℕ) : ℤ) = (n : ℤ)-j.val := by omega
  have hnk : (k : ℤ)*(k+2) ≤ n := by exact_mod_cast hn
  by_cases h : 2*j.val ≤ n
  · have hf : f n k j ≤ lineCost k j.val := min_le_left _ _
    have hb := lineCost_upper hk j.val
    have hp := mul_nonneg (show 0 ≤ (k : ℤ) by omega)
      (show 0 ≤ (lineCost k j.val : ℤ)-(f n k j : ℤ) by omega)
    nlinarith
  · have hf : f n k j ≤ lineCost k (n-j.val) := min_le_right _ _
    have hb := lineCost_upper hk (n-j.val)
    have hp := mul_nonneg (show 0 ≤ (k : ℤ) by omega)
      (show 0 ≤ (lineCost k (n-j.val) : ℤ)-(f n k j : ℤ) by omega)
    nlinarith

theorem lift_split (j : ZMod n) (y : ℤ) (hy : (y : ZMod n) = j) :
    y = j.val ∨ y = (j.val : ℤ)-n ∨ (n : ℤ) ≤ |y| := by
  have hz : ((y-(j.val : ℤ) : ℤ) : ZMod n) = 0 := by
    push_cast
    rw [hy, ZMod.natCast_zmod_val]
    simp
  obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hj := j.val_lt
  have hn := NeZero.pos n
  by_cases h0 : c = 0
  · left; rw [h0] at hc; simp only [mul_zero] at hc; omega
  · by_cases h1 : c = -1
    · right; left; rw [h1] at hc; omega
    · right; right
      have hpos := le_abs_self y
      have hneg := neg_le_abs y
      by_cases hp : 1 ≤ c
      · have hm := mul_nonneg (show 0 ≤ (n : ℤ) by omega) (show 0 ≤ c-1 by omega)
        nlinarith
      · have hm := mul_nonneg (show 0 ≤ (n : ℤ) by omega) (show 0 ≤ -c-2 by omega)
        nlinarith

theorem cost_lift_bound (hk : 1 ≤ k) (a b : ℤ) :
    |a+(k : ℤ)*b| ≤ (k : ℤ)*(a.natAbs+b.natAbs : ℕ) := by
  rw [Nat.cast_add, Int.natCast_natAbs, Int.natCast_natAbs]
  have h := abs_add_le a ((k : ℤ)*b)
  rw [abs_mul, abs_of_nonneg (show 0 ≤ (k : ℤ) by omega)] at h
  have hp := mul_nonneg (show 0 ≤ (k : ℤ)-1 by omega) (abs_nonneg a)
  nlinarith

theorem cyclic_lower (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) (a b : ℤ)
    (he : (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j) :
    f n k j ≤ a.natAbs+b.natAbs := by
  have hy : ((a+(k : ℤ)*b : ℤ) : ZMod n) = j := by push_cast; exact he
  rcases lift_split j (a+(k : ℤ)*b) hy with h | h | h
  · exact (min_le_left _ _).trans ((lineCost_min hk j.val).2 a b h)
  · have hj := j.val_lt
    have he' : -a+(k : ℤ)*(-b) = (n-j.val : ℕ) := by
      rw [Nat.cast_sub (by omega : j.val ≤ n)]
      linarith
    have hl := (lineCost_min hk (n-j.val)).2 (-a) (-b) he'
    simpa only [f, Int.natAbs_neg] using (min_le_right (lineCost k j.val) (lineCost k (n-j.val))).trans hl
  · have hf := f_short hk hn j
    have hb := cost_lift_bound (by omega : 1 ≤ k) a b
    by_contra hc
    have hp := mul_nonneg (show 0 ≤ (k : ℤ) by omega)
      (show 0 ≤ (f n k j : ℤ)-(a.natAbs+b.natAbs : ℕ) by omega)
    nlinarith

theorem word_eq_f (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) :
    word n k j = f n k j := by
  apply Nat.le_antisymm
  · unfold f
    apply le_min
    · obtain ⟨a,b,he,hl⟩ := (lineCost_min hk j.val).1
      have hc : (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = j := by
        have hh := congrArg (fun z : ℤ => (z : ZMod n)) he
        push_cast at hh
        simpa using hh
      exact hl ▸ word_le j a b hc
    · obtain ⟨a,b,he,hl⟩ := (lineCost_min hk (n-j.val)).1
      have hc : ((-a : ℤ) : ZMod n)+(k : ZMod n)*((-b : ℤ) : ZMod n) = j := by
        have hh := congrArg (fun z : ℤ => (z : ZMod n)) he
        push_cast at hh
        have hj := j.val_lt
        rw [Nat.cast_sub (by omega : j.val ≤ n), ZMod.natCast_self, ZMod.natCast_zmod_val] at hh
        push_cast
        calc
          _ = -( (a : ZMod n)+(k : ZMod n)*(b : ZMod n)) := by ring
          _ = j := by rw [hh]; ring
      have hw := word_le j (-a) (-b) hc
      simpa [hl] using hw
  · obtain ⟨a,b,he,hl⟩ := word_exists (k := k) j
    rw [← hl]
    exact cyclic_lower hk hn j a b he

#print axioms word_eq_f
end Petersen
```

### `PetersenDistance.lean`

```lean
import PetersenCyclic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem outer_min (j : ZMod n) :
  (∃ a : ℤ, (a : ZMod n) = j ∧ a.natAbs = p n j) ∧
  (∀ a : ℤ, (a : ZMod n) = j → p n j ≤ a.natAbs) := by
  have hj := j.val_lt
  have hcast : (((n-j.val : ℕ) : ℤ) : ZMod n) = -j := by
    rw [Int.cast_natCast, Nat.cast_sub (by omega : j.val ≤ n), ZMod.natCast_self, ZMod.natCast_zmod_val]
    simp
  constructor
  · by_cases h : j.val ≤ n-j.val
    · exact ⟨(j.val : ℤ), by simp, by simpa only [p, min_eq_left h, Int.natAbs_natCast]⟩
    · refine ⟨-((n-j.val : ℕ) : ℤ), ?_, ?_⟩
      · rw [Int.cast_neg, hcast, neg_neg]
      · simp only [p, min_eq_right (by omega : n-j.val ≤ j.val), Int.natAbs_neg, Int.natAbs_natCast]
  · intro a ha
    rcases lift_split j a ha with h | h | h
    · rw [h, Int.natAbs_natCast]
      exact min_le_left _ _
    · have he : a = -((n-j.val : ℕ) : ℤ) := by rw [Nat.cast_sub (by omega : j.val ≤ n)]; omega
      rw [he, Int.natAbs_neg, Int.natAbs_natCast]
      exact min_le_right _ _
    · have hp : p n j ≤ n := (min_le_left j.val (n-j.val)).trans (by omega)
      have hn : n ≤ a.natAbs := by rw [← Int.natCast_natAbs] at h; exact_mod_cast h
      exact hp.trans hn

theorem pure_outer (j : ZMod n) : pure n 1 j = (p n j : ℕ∞) := by
  apply le_antisymm
  · obtain ⟨a,ha,hl⟩ := (outer_min j).1
    rw [← hl]
    apply pure_le
    simpa using ha
  · apply le_iInf
    intro a
    have ha : (a.val : ZMod n) = j := by simpa using a.property
    exact_mod_cast (outer_min j).2 a.val ha

/-- The explicit formula used in all subsequent balance arithmetic. -/
theorem distance_formula (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i j : ZMod n) :
  (GP n k).dist (false,i) (true,j) = f n k (j-i)+1 ∧
  (GP n k).dist (false,i) (false,j) = min (p n (j-i)) (f n k (j-i)+2) ∧
  (GP n k).dist (true,i) (true,j) =
    (min (t n k (j-i)) ((f n k (j-i)+2 : ℕ) : ℕ∞)).toNat := by
  have hf := word_eq_f hk hn (j-i)
  refine ⟨?_, ?_, ?_⟩
  · rw [dist_mixed_word, hf]
  · have h := dist_same_word (k := k) false i j
    have hs : step (n := n) k false = 1 := rfl
    rw [hs, pure_outer, hf] at h
    by_cases hp : p n (j-i) ≤ f n k (j-i)+2
    · rw [min_eq_left (by exact_mod_cast hp)] at h
      rw [min_eq_left hp]
      exact_mod_cast h
    · have hp' : f n k (j-i)+2 ≤ p n (j-i) := by omega
      rw [min_eq_right (by exact_mod_cast hp')] at h
      rw [min_eq_right hp']
      exact_mod_cast h
  · have h := dist_same_word (k := k) true i j
    have hs : step (n := n) k true = (k : ZMod n) := rfl
    rw [hs, hf] at h
    have h' := congrArg ENat.toNat h
    simpa only [ENat.toNat_natCast, t] using h'

theorem eventual_connected :
    ∀ k (_hk : 2 ≤ k), ∀ n (hn : nk k < n),
      letI : NeZero n := ⟨by omega⟩
      (GP n k).Connected := by
  intro k hk n hn
  let _ : NeZero n := ⟨by omega⟩
  exact gp_connected n k

#check distance_formula
#print axioms distance_formula
#print axioms eventual_connected
#print MiklavicSparl44
end Petersen
```

### `PetersenArithmetic.lean`

```lean
import PetersenDistance

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ}

theorem nk_eq (hk : 3 ≤ k) : nk k = k*(k+2)+k%2 := by
  unfold nk
  rw [ite_eq_right (by omega : k ≠ 2)]
  by_cases ho : Odd k
  · rw [ite_eq_left ho, Nat.odd_iff.mp ho]
    ring
  · rw [ite_eq_right ho, Nat.not_odd_iff.mp ho]
    omega

theorem threshold_quotient (hk : 3 ≤ k) :
    nk k < n ↔ k+2 ≤ n/k ∧ (n/k = k+2 → k%2 < n%k) := by
  rw [nk_eq hk]
  have hd := Nat.div_add_mod n k
  have hr := Nat.mod_lt n (by omega : 0 < k)
  constructor
  · intro hn
    have hq : k+2 ≤ n/k := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr
      rw [Nat.mul_comm]
      omega
    exact ⟨hq, by intro h; rw [h] at hd; omega⟩
  · rintro ⟨hq,hrq⟩
    by_cases h : n/k = k+2
    · have hrr := hrq h
      rw [h] at hd
      omega
    · have hp : (k+3)*k ≤ n := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp (by omega : k+3 ≤ n/k)
      have hm := Nat.mod_lt k (by decide : 0 < 2)
      nlinarith

theorem threshold_metric (hk : 2 ≤ k) (hn : nk k < n) : k*(k+2) ≤ n := by
  by_cases h2 : k = 2
  · subst k
    norm_num [nk] at hn ⊢
    omega
  · have h := nk_eq (by omega : 3 ≤ k)
    omega

theorem threshold_admissible (hk : 2 ≤ k) (hn : nk k ≤ n) : 3 ≤ n ∧ 2*k < n := by
  by_cases h2 : k = 2
  · subst k
    norm_num [nk] at hn ⊢
    omega
  · have he := nk_eq (by omega : 3 ≤ k)
    constructor <;> nlinarith [Nat.zero_le (k%2)]

variable [NeZero n]

/-- Maximum cyclic ±1,±k word radius; no diameter formula is assumed. -/
def F (n k : ℕ) [NeZero n] : ℕ := Finset.univ.sup (f n k)

theorem f_le_F (j : ZMod n) : f n k j ≤ F n k :=
  Finset.le_sup (f := f n k) (Finset.mem_univ j)

theorem diam_le_F_add_two (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) :
    (GP n k).diam ≤ F n k+2 := by
  obtain ⟨⟨a,i⟩,⟨b,j⟩,he⟩ := (GP n k).exists_dist_eq_diam
  rw [← he]
  have huv : (GP n k).dist (false,i) (true,j) ≤ F n k+2 := by
    rw [(distance_formula hk hn i j).1]
    have := f_le_F (k := k) (j-i)
    omega
  have hvu : (GP n k).dist (true,i) (false,j) ≤ F n k+2 := by
    rw [SimpleGraph.dist_comm]
    rw [(distance_formula hk hn j i).1]
    have := f_le_F (k := k) (i-j)
    omega
  have hs (b : Bool) : (GP n k).dist (b,i) (b,j) ≤ F n k+2 := by
    have h := dist_same_word (k := k) b i j
    have hle : ((GP n k).dist (b,i) (b,j) : ℕ∞) ≤ ((word n k (j-i)+2 : ℕ) : ℕ∞) := by
      rw [h]; exact min_le_right _ _
    have hnat : (GP n k).dist (b,i) (b,j) ≤ word n k (j-i)+2 := by exact_mod_cast hle
    rw [word_eq_f hk hn] at hnat
    exact hnat.trans (Nat.add_le_add_right (f_le_F _) 2)
  cases a <;> cases b
  · exact hs false
  · exact huv
  · exact hvu
  · exact hs true

#print axioms threshold_quotient
#print axioms diam_le_F_add_two
end Petersen
```

### `PetersenWordArithmetic.lean`

```lean
import PetersenArithmetic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem word_zero : word n k 0 = 0 := by
  have h := word_le (n := n) (k := k) 0 0 0 (by simp)
  simpa using h

theorem word_neg_le (j : ZMod n) : word n k (-j) ≤ word n k j := by
  obtain ⟨a,b,he,hl⟩ := word_exists (k := k) j
  have hc : ((-a : ℤ) : ZMod n)+(k : ZMod n)*((-b : ℤ) : ZMod n) = -j := by
    push_cast
    calc
      _ = -((a : ZMod n)+(k : ZMod n)*(b : ZMod n)) := by ring
      _ = -j := by rw [he]
  have h := word_le (-j) (-a) (-b) hc
  simpa only [Int.natAbs_neg, hl] using h

theorem word_neg (j : ZMod n) : word n k (-j) = word n k j := by
  apply Nat.le_antisymm (word_neg_le j)
  simpa using word_neg_le (k := k) (-j)

theorem word_add_le (i j : ZMod n) : word n k (i+j) ≤ word n k i+word n k j := by
  obtain ⟨a,b,he,hl⟩ := word_exists (k := k) i
  obtain ⟨c,d,he',hl'⟩ := word_exists (k := k) j
  have hc : ((a+c : ℤ) : ZMod n)+(k : ZMod n)*((b+d : ℤ) : ZMod n) = i+j := by
    push_cast
    calc
      _ = ((a : ZMod n)+(k : ZMod n)*(b : ZMod n))+
          ((c : ZMod n)+(k : ZMod n)*(d : ZMod n)) := by ring
      _ = i+j := by rw [he,he']
  have h := word_le (i+j) (a+c) (b+d) hc
  have ha := Int.natAbs_add_le a c
  have hb := Int.natAbs_add_le b d
  omega

theorem f_zero (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) : f n k 0 = 0 := by
  rw [← word_eq_f hk hn, word_zero]

theorem f_neg (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) : f n k (-j) = f n k j := by
  rw [← word_eq_f hk hn, ← word_eq_f hk hn, word_neg]

theorem f_add_le (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i j : ZMod n) :
    f n k (i+j) ≤ f n k i+f n k j := by
  simpa only [word_eq_f hk hn] using word_add_le (k := k) i j

theorem f_generator_le_one (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (s : ZMod n)
    (hs : s = 1 ∨ s = (k : ZMod n) ∨ s = -1 ∨ s = -(k : ZMod n)) :
    f n k s ≤ 1 := by
  rw [← word_eq_f hk hn]
  have h1 : word n k 1 ≤ 1 := by
    simpa using word_le (n := n) (k := k) 1 1 0 (by simp)
  have hk' : word n k (k : ZMod n) ≤ 1 := by
    simpa using word_le (n := n) (k := k) (k : ZMod n) 0 1 (by simp)
  rcases hs with rfl | rfl | rfl | rfl
  · exact h1
  · exact hk'
  · rw [word_neg]; exact h1
  · rw [word_neg]; exact hk'

theorem f_step_bound (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j s : ZMod n)
    (hs : s = 1 ∨ s = (k : ZMod n) ∨ s = -1 ∨ s = -(k : ZMod n)) :
    f n k (j+s) ≤ f n k j+1 ∧ f n k j ≤ f n k (j+s)+1 := by
  have hu := f_add_le hk hn j s
  have hs' := f_generator_le_one hk hn s hs
  have hl := f_add_le hk hn (j+s) (-s)
  rw [f_neg hk hn] at hl
  have he : j+s+-s = j := by abel
  rw [he] at hl
  omega

#print axioms f_step_bound
end Petersen
```

### `PetersenRadii.lean`

```lean
import PetersenWordArithmetic

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem f_adj_bounds (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) {x y : Bool × ZMod n}
    (h : (GP n k).Adj x y) :
    f n k y.2 ≤ f n k x.2+1 ∧ f n k x.2 ≤ f n k y.2+1 := by
  rcases h.2 with h | h
  · rcases h with h | h | h
    · rw [h.2.2]
      exact f_step_bound hk hn x.2 1 (Or.inl rfl)
    · rw [h.2.2]
      exact f_step_bound hk hn x.2 (k : ZMod n) (Or.inr (Or.inl rfl))
    · rw [h.2.2]; omega
  · rcases h with h | h | h
    · rw [h.2.2]
      have ht := f_step_bound hk hn y.2 1 (Or.inl rfl)
      exact ⟨ht.2,ht.1⟩
    · rw [h.2.2]
      have ht := f_step_bound hk hn y.2 (k : ZMod n) (Or.inr (Or.inl rfl))
      exact ⟨ht.2,ht.1⟩
    · rw [h.2.2]; omega

/-- A unit-Lipschitz integer function attains every intermediate level along a walk. -/
theorem walk_hits_level {V : Type*} {G : SimpleGraph V} (phi : V → ℕ)
    (hstep : ∀ {x y}, G.Adj x y → phi y ≤ phi x+1) {x y : V} (w : G.Walk x y) :
    ∀ a, phi x ≤ a → a ≤ phi y → ∃ z, phi z = a := by
  induction w with
  | @nil x => intro a hlo hhi; exact ⟨x, by omega⟩
  | @cons x y z h w ih =>
    intro a hlo hhi
    by_cases he : phi x = a
    · exact ⟨x,he⟩
    · have hy := hstep h
      exact ih a (by omega) hhi

theorem radius_attained (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (a : ℕ) (ha : a ≤ F n k) :
    ∃ j : ZMod n, f n k j = a := by
  have hex : ∃ j : ZMod n, f n k j = F n k := by
    obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (f n k)
    exact ⟨j,hj.symm⟩
  obtain ⟨j,hj⟩ := hex
  obtain ⟨w⟩ := (gp_connected n k) (false,0) (false,j)
  have h := walk_hits_level (fun x : Bool × ZMod n => f n k x.2)
    (fun h => (f_adj_bounds hk hn h).1) w a (by simpa [f_zero hk hn]) (by simpa [hj] using ha)
  obtain ⟨z,hz⟩ := h
  exact ⟨z.2,hz⟩

theorem subdiam_radius (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (ell : ℕ)
    (h1 : 1 ≤ ell) (hD : ell < (GP n k).diam) :
    ∃ j : ZMod n, f n k j = ell-1 := by
  have hd := diam_le_F_add_two hk hn
  exact radius_attained hk hn (ell-1) (by omega)

#print axioms subdiam_radius
end Petersen
```

### `PetersenAudit.lean`

```lean
import PetersenSanity
import PetersenRadii

namespace Petersen
#print GP
#print nk
#print W
#print LDB
#print MiklavicSparl44
#check gp_connected
#check eventual_connected
#check petersen_card
#check petersen_cubic
#check petersen_diam
#check distance_formula
#check subdiam_radius
#check threshold_quotient
#check threshold_admissible
#print axioms GP
#print axioms nk
#print axioms W
#print axioms LDB
#print axioms MiklavicSparl44
#print axioms gp_connected
#print axioms eventual_connected
#print axioms petersen_card
#print axioms petersen_cubic
#print axioms petersen_diam
#print axioms distance_formula
#print axioms subdiam_radius
#print axioms threshold_quotient
#print axioms threshold_admissible
#print axioms diam_le_F_add_two
#print axioms f_step_bound
end Petersen

-- Runtime version printed by the bounded compiler; no proof uses evaluation.
#eval Lean.versionString
```

### `PetersenSymmetry.lean`

```lean
import PetersenWalks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- The reflection of both layers about the index a/2. -/
def reflection (a : ZMod n) : (Bool × ZMod n) ≃ (Bool × ZMod n) where
  toFun x := (x.1, a-x.2)
  invFun x := (x.1, a-x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

private theorem reflection_adj (a : ZMod n) (x y : Bool × ZMod n)
    (h : (GP n k).Adj x y) :
    (GP n k).Adj (reflection a x) (reflection a y) := by
  obtain ⟨hne, hr | hr⟩ := h
  · refine ⟨fun he => hne ((reflection a).injective he), ?_⟩
    rcases hr with ⟨hx, hy, he⟩ | ⟨hx, hy, he⟩ | ⟨hx, hy, he⟩
    · right; left; exact ⟨hy, hx, by change a-x.2 = a-y.2+1; rw [he]; ring⟩
    · right; right; left; exact ⟨hy, hx, by change a-x.2 = a-y.2+k; rw [he]; ring⟩
    · left; right; right; exact ⟨hx, hy, by change a-y.2 = a-x.2; rw [he]⟩
  · exact (reflection_adj_forward hne hr).symm
where
  reflection_adj_forward {x y : Bool × ZMod n}
      (hne : y ≠ x) (hr : (x.1 = false ∧ y.1 = false ∧ y.2 = x.2+1) ∨
        (x.1 = true ∧ y.1 = true ∧ y.2 = x.2+(k : ZMod n)) ∨
        (x.1 = false ∧ y.1 = true ∧ y.2 = x.2)) :
      (GP n k).Adj (reflection a x) (reflection a y) := by
    refine ⟨fun he => hne ((reflection a).injective he.symm), ?_⟩
    rcases hr with ⟨hx, hy, he⟩ | ⟨hx, hy, he⟩ | ⟨hx, hy, he⟩
    · right; left; exact ⟨hy, hx, by change a-x.2 = a-y.2+1; rw [he]; ring⟩
    · right; right; left; exact ⟨hy, hx, by change a-x.2 = a-y.2+k; rw [he]; ring⟩
    · left; right; right; exact ⟨hx, hy, by change a-y.2 = a-x.2; rw [he]⟩

/-- A genuine graph automorphism, with no range hypothesis on k. -/
def reflectionIso (a : ZMod n) : GP n k ≃g GP n k where
  toEquiv := reflection a
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have h' := reflection_adj a (reflection a x) (reflection a y) h
      simpa [reflection] using h'
    · exact reflection_adj a x y

theorem iso_dist {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (e : G ≃g G) (x y : V) : G.dist (e x) (e y) = G.dist x y := by
  apply Nat.le_antisymm
  · obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist x y
    have h := G.dist_le (w.map e.toHom)
    simpa [hw] using h
  · obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist (e x) (e y)
    have h := G.dist_le (w.map e.symm.toHom)
    simpa [hw] using h

theorem iso_W_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (e : G ≃g G) (x y : V) :
    (W G (e x) (e y)).card = (W G x y).card := by
  classical
  symm
  apply Finset.card_bij (fun w _ => e w)
  · intro w hw
    simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and, iso_dist hc e] using hw
  · intro w _ z _ he
    exact e.injective he
  · intro w hw
    obtain ⟨z, rfl⟩ := e.surjective w
    refine ⟨z, ?_, rfl⟩
    simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and, iso_dist hc e] using hw

theorem same_layer_balanced (layer : Bool) (i j : ZMod n) :
    (W (GP n k) (layer,i) (layer,j)).card =
      (W (GP n k) (layer,j) (layer,i)).card := by
  have h := iso_W_card (gp_connected n k) (reflectionIso (i+j)) (layer,i) (layer,j)
  simpa [reflectionIso, reflection] using h.symm

end Petersen
```

### `PetersenBalanceCounts.lean`

```lean
import PetersenDistance
import PetersenWordArithmetic
import PetersenSymmetry
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

def sign (x : ℤ) : ℤ := if 0 < x then 1 else if x = 0 then 0 else -1

def outerProfile (n k : ℕ) [NeZero n] (i : ZMod n) : ℕ := min (p n i) (f n k i+2)
noncomputable def innerProfile (n k : ℕ) [NeZero n] (i : ZMod n) : ℕ :=
  (min (t n k i) ((f n k i+2 : ℕ) : ℕ∞)).toNat

theorem profiles (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i j : ZMod n) :
    (GP n k).dist (false,i) (true,j) = f n k (j-i)+1 ∧
    (GP n k).dist (false,i) (false,j) = outerProfile n k (j-i) ∧
    (GP n k).dist (true,i) (true,j) = innerProfile n k (j-i) :=
  distance_formula hk hn i j

/-- Number closer to u_0 than v_j, on the two layers, using the distance formula. -/
noncomputable def closerCount (n k : ℕ) [NeZero n] (j : ZMod n) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => outerProfile n k i < f n k (i-j)+1).card +
    (Finset.univ.filter fun i => f n k i+1 < innerProfile n k (i-j)).card

noncomputable def fartherCount (n k : ℕ) [NeZero n] (j : ZMod n) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => f n k (i-j)+1 < outerProfile n k i).card +
    (Finset.univ.filter fun i => innerProfile n k (i-j) < f n k i+1).card

noncomputable def imbalance (n k : ℕ) [NeZero n] (j : ZMod n) : ℤ :=
  ((W (GP n k) (false,0) (true,j)).card : ℤ) -
    ((W (GP n k) (true,j) (false,0)).card : ℤ)

noncomputable def outerCount (n k : ℕ) [NeZero n] (j : ZMod n) : ℤ :=
  ∑ i : ZMod n,
    (sign (((f n k (i-j)+1 : ℕ) : ℤ) - (outerProfile n k i : ℤ)) -
      sign (((f n k (i-j)+1 : ℕ) : ℤ) - ((f n k i+2 : ℕ) : ℤ)))
noncomputable def innerCount (n k : ℕ) [NeZero n] (j : ZMod n) : ℤ :=
  ∑ i : ZMod n,
    (sign (((f n k (i-j)+1 : ℕ) : ℤ) - (innerProfile n k i : ℤ)) -
      sign (((f n k (i-j)+1 : ℕ) : ℤ) - ((f n k i+2 : ℕ) : ℤ)))

private theorem card_layers (P : Bool × ZMod n → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun i => P (false,i)).card +
      (Finset.univ.filter fun i => P (true,i)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  omega

theorem closerCount_eq (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) :
    closerCount n k j = (W (GP n k) (false,0) (true,j)).card ∧
    fartherCount n k j = (W (GP n k) (true,j) (false,0)).card := by
  classical
  have hm (i : ZMod n) : (GP n k).dist (true,j) (false,i) = f n k (i-j)+1 := by
    rw [SimpleGraph.dist_comm, (profiles hk hn i j).1]
    rw [← neg_sub i j, f_neg hk hn]
  constructor <;>
    simp only [W, card_layers, closerCount, fartherCount, hm,
      (profiles hk hn 0 _).1, (profiles hk hn 0 _).2.1,
      (profiles hk hn j _).2.2, sub_zero]

theorem sign_difference (a b : ℕ) :
    sign ((b : ℤ)-a) = (if a < b then 1 else 0 : ℤ) - (if b < a then 1 else 0) := by
  unfold sign
  split_ifs <;> omega

/-- An integer sign sum is exactly the difference of the two strict counts. -/
theorem W_difference {V : Type*} [Fintype V] (G : SimpleGraph V) (x y : V) :
    ((W G x y).card : ℤ) - ((W G y x).card : ℤ) =
      ∑ w : V, sign ((G.dist y w : ℤ)-G.dist x w) := by
  classical
  simp only [sign_difference, Finset.sum_sub_distrib, Finset.sum_boole, W]

theorem innerProfile_neg (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n) :
    innerProfile n k (-i) = innerProfile n k i := by
  have h := iso_dist (gp_connected n k) (reflectionIso 0) (true,0) (true,i)
  simpa [reflectionIso, reflection, (profiles hk hn 0 _).2.2] using h

theorem outerProfile_neg (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n) :
    outerProfile n k (-i) = outerProfile n k i := by
  have h := iso_dist (gp_connected n k) (reflectionIso 0) (false,0) (false,i)
  simpa [reflectionIso, reflection, (profiles hk hn 0 _).2.1] using h

theorem sign_neg (x : ℤ) : sign (-x) = -sign x := by
  unfold sign
  split_ifs <;> omega

theorem sum_reflect (j : ZMod n) (g : ZMod n → ℤ) :
    ∑ i : ZMod n, g (j-i) = ∑ i : ZMod n, g i := by
  let e : ZMod n ≃ ZMod n :=
    { toFun := fun i => j-i
      invFun := fun i => j-i
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  exact e.sum_comp g

/-- Formula (5), with both sides referring to the literal GP graph. -/
theorem cancellation (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) :
    imbalance n k j = outerCount n k j - innerCount n k j := by
  classical
  have hm (i : ZMod n) : (GP n k).dist (true,j) (false,i) = f n k (i-j)+1 := by
    rw [SimpleGraph.dist_comm, (profiles hk hn i j).1]
    rw [← neg_sub i j, f_neg hk hn]
  have hraw : imbalance n k j =
      (∑ i : ZMod n, sign (((f n k (i-j)+1 : ℕ) : ℤ) - (outerProfile n k i : ℤ))) +
      (∑ i : ZMod n, sign ((innerProfile n k (i-j) : ℤ) - ((f n k i+1 : ℕ) : ℤ))) := by
    unfold imbalance
    rw [W_difference, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hm, (profiles hk hn 0 _).1, (profiles hk hn 0 _).2.1,
      (profiles hk hn j _).2.2, sub_zero]
    ring
  have hi : (∑ i : ZMod n,
      sign ((innerProfile n k (i-j) : ℤ) - ((f n k i+1 : ℕ) : ℤ))) =
      -(∑ i : ZMod n,
      sign (((f n k (i-j)+1 : ℕ) : ℤ) - (innerProfile n k i : ℤ))) := by
    rw [← sum_reflect j (fun i =>
      sign ((innerProfile n k (i-j) : ℤ) - ((f n k i+1 : ℕ) : ℤ)))]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have he : j-i-j = -i := by ring
    rw [he, innerProfile_neg hk hn, ← neg_sub i j, f_neg hk hn]
    convert sign_neg (((f n k (i-j)+1 : ℕ) : ℤ) - (innerProfile n k i : ℤ)) using 1; congr 1; ring
  rw [hraw, hi]
  simp only [outerCount, innerCount, Finset.sum_sub_distrib]
  ring

/-- One strict mixed imbalance disproves balance for its exact distance. -/
theorem not_LDB_of_imbalance (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n)
    (hj : imbalance n k j ≠ 0) : ¬ LDB (GP n k) (f n k j+1) := by
  intro h
  have hcard := h (false,0) (true,j) (by simpa using (profiles hk hn 0 j).1)
  apply hj
  simp [imbalance, hcard]

end Petersen
```

### `PetersenOuterSupport.lean`

```lean
import PetersenBalanceCounts

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- A cyclic index may be replaced by its nearer nonnegative lift. -/
theorem f_near (i : ZMod n) :
    f n k i = min (lineCost k (p n i)) (lineCost k (n-p n i)) := by
  rcases le_total i.val (n-i.val) with h | h
  · have hp : p n i = i.val := min_eq_left h
    rw [hp]; rfl
  · have hp : p n i = n-i.val := min_eq_right h
    rw [hp]
    have he : n-(n-i.val) = i.val := by have := i.val_lt; omega
    rw [he, min_comm]; rfl

theorem lineCost_displacement (hk : 2 ≤ k) (s : ℕ) : s ≤ k*lineCost k s := by
  obtain ⟨a,b,he,hab⟩ := (lineCost_min hk s).1
  have h := cost_lift_bound (by omega : 1 ≤ k) a b
  rw [he, hab] at h
  exact_mod_cast h

theorem lineCost_short (_hk : 0 < k) {s : ℕ} (hs : s < k) : lineCost k s = H k s := by
  simp [lineCost, Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hs]

theorem f_short_near (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n)
    (hi : p n i < k) : f n k i = H k (p n i) := by
  have hp := show p n i ≤ i.val from min_le_left _ _
  have hval := i.val_lt
  have hb := lineCost_displacement (by omega : 2 ≤ k) (n-p n i)
  have hh : H k (p n i) ≤ p n i := min_le_left _ _
  have hl : k ≤ lineCost k (n-p n i) := by
    by_contra h
    have hx : lineCost k (n-p n i) ≤ k-1 := by omega
    have hm := Nat.mul_le_mul_left k hx
    have hnsub : n-p n i+p n i = n := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [f_near, lineCost_short (by omega : 0 < k) hi, min_eq_left (by omega)]

/-- Outside the short strip the pure outer route cannot improve f+2. -/
theorem lineCost_long (hk : 3 ≤ k) {s : ℕ} (hs : k/2+2 ≤ s) :
    lineCost k s+2 ≤ s := by
  by_cases hsk : s < k
  · rw [lineCost_short (by omega : 0 < k) hsk]
    have hb : H k s ≤ k+1-s := min_le_right _ _
    have hd := Nat.mod_lt k (by omega : 0 < 2)
    have he := Nat.mod_add_div k 2
    omega
  · have hq : 1 ≤ s/k := Nat.one_le_div_iff (by omega) |>.mpr (by omega)
    have hr := Nat.mod_lt s (by omega : 0 < k)
    have he := Nat.div_add_mod s k
    have hb : H k (s%k) ≤ s%k := min_le_left _ _
    have hm := Nat.mul_le_mul_left (s/k) hk
    unfold lineCost
    nlinarith

/-- Exact support of the outer shortcut, including the common origin. -/
theorem outer_shortcut_iff (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n) :
    outerProfile n k i < f n k i+2 ↔ p n i ≤ k/2+1 := by
  by_cases hs : p n i ≤ k/2+1
  · have hi : p n i < k := by omega
    have hf := f_short_near hk hn i hi
    have hgap : p n i < H k (p n i)+2 := by unfold H; omega
    have hprof : outerProfile n k i = p n i := by
      unfold outerProfile; rw [hf]; exact min_eq_left (by omega)
    rw [hprof, hf]
    exact iff_of_true hgap hs
  · have hl := lineCost_long hk (s := p n i) (by omega)
    have hf : f n k i ≤ lineCost k (p n i) := by rw [f_near]; exact min_le_left _ _
    have he : outerProfile n k i = f n k i+2 := min_eq_right (by omega)
    rw [he]
    omega

/-- Pure length and f-value at each outer shortcut; this includes s=0. -/
theorem outer_shortcut_values (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n)
    (hi : p n i ≤ k/2+1) :
    outerProfile n k i = p n i ∧ f n k i = H k (p n i) := by
  have hf := f_short_near hk hn i (by omega)
  refine ⟨?_, hf⟩
  have hs := (outer_shortcut_iff hk hn i).2 hi
  unfold outerProfile at hs ⊢
  omega

end Petersen
```

### `PetersenPulses.lean`

```lean
import PetersenOuterSupport

namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

def pulse (a b c : ℤ) : ℤ := sign (c-a)-sign (c-b)
def K (x : ℤ) : ℤ := if x = 0 then 2 else if x = 1 ∨ x = -1 then 1 else 0

theorem pulse_nonneg (a b c : ℤ) (hab : a ≤ b) : 0 ≤ pulse a b c := by
  unfold pulse sign
  split_ifs <;> omega

theorem pulse_left_antitone (a a' b c : ℤ) (haa : a ≤ a') :
    pulse a' b c ≤ pulse a b c := by
  unfold pulse sign
  split_ifs <;> omega

theorem pulse_min_bound (a b c d : ℤ) (hab : a ≤ b) :
    pulse a b (min c d) ≤ pulse a b c + pulse a b d := by
  have hc := pulse_nonneg a b c hab
  have hd := pulse_nonneg a b d hab
  rcases le_total c d with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

theorem pulse_full (f t : ℤ) : pulse t (t+2) (1+f) = K (f-t) := by
  unfold pulse sign K
  split_ifs <;> omega

theorem K_nonneg (x : ℤ) : 0 ≤ K x := by unfold K; split_ifs <;> omega

noncomputable def outerPulse (n k : ℕ) [NeZero n] (j i : ZMod n) : ℤ :=
  pulse (outerProfile n k i) (f n k i+2) (f n k (i-j)+1)
noncomputable def innerPulse (n k : ℕ) [NeZero n] (j i : ZMod n) : ℤ :=
  pulse (innerProfile n k i) (f n k i+2) (f n k (i-j)+1)

theorem outerCount_sum (j : ZMod n) : outerCount n k j = ∑ i, outerPulse n k j i := by
  simp only [outerCount, outerPulse, pulse, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
theorem innerCount_sum (j : ZMod n) : innerCount n k j = ∑ i, innerPulse n k j i := by
  simp only [innerCount, innerPulse, pulse, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

theorem innerProfile_le (i : ZMod n) : innerProfile n k i ≤ f n k i+2 :=
  ENat.toNat_le_of_le_natCast (min_le_right _ _)

theorem outerPulse_nonneg (j i : ZMod n) : 0 ≤ outerPulse n k j i := by
  apply pulse_nonneg
  exact_mod_cast (min_le_right _ _ : outerProfile n k i ≤ f n k i+2)
theorem innerPulse_nonneg (j i : ZMod n) : 0 ≤ innerPulse n k j i := by
  apply pulse_nonneg
  exact_mod_cast innerProfile_le i

theorem outerPulse_vanish (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (j i : ZMod n)
    (hi : k/2+1 < p n i) : outerPulse n k j i = 0 := by
  have h := (outer_shortcut_iff hk hn i).not.mpr (by omega)
  have he : outerProfile n k i = f n k i+2 := by
    have hl : outerProfile n k i ≤ f n k i+2 := min_le_right _ _
    omega
  simp [outerPulse, he, pulse]

/-- A pure inner route is enough for a lower bound; no pure-minimum classification is needed. -/
theorem innerProfile_le_route (z : ℤ) :
    innerProfile n k ((k : ZMod n)*(z : ZMod n)) ≤ z.natAbs := by
  apply ENat.toNat_le_of_le_natCast
  exact (min_le_left _ _).trans (pure_le _ _ z rfl)

/-- Full-deficit kernel lower bound at any chosen inner route. -/
theorem innerPulse_route (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (j : ZMod n) (z : ℤ) (hf : f n k ((k : ZMod n)*(z : ZMod n)) = z.natAbs) :
    K ((f n k (j-(k : ZMod n)*(z : ZMod n)) : ℤ)-z.natAbs) ≤
      innerPulse n k j ((k : ZMod n)*(z : ZMod n)) := by
  have hp := innerProfile_le_route (n := n) (k := k) z
  unfold innerPulse
  rw [hf, ← neg_sub j _, f_neg hk hn]
  have h := pulse_left_antitone
    (innerProfile n k ((k : ZMod n)*(z : ZMod n))) z.natAbs (z.natAbs+2)
    (1+(f n k (j-(k : ZMod n)*(z : ZMod n)) : ℤ)) (by exact_mod_cast hp)
  rw [pulse_full] at h
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_comm] using h

/-- An injective finite selection of routes gives a certified lower count. -/
theorem innerCount_selected {ι : Type*} [Fintype ι] (j : ZMod n)
    (idx : ι → ZMod n) (hinj : Function.Injective idx) :
    (∑ a, innerPulse n k j (idx a)) ≤ innerCount n k j := by
  classical
  rw [innerCount_sum]
  calc
    _ = ∑ i ∈ Finset.univ.image idx, innerPulse n k j i :=
      (Finset.sum_image (fun a _ b _ h => hinj h)).symm
    _ ≤ ∑ i : ZMod n, innerPulse n k j i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact innerPulse_nonneg j i

theorem strict_imbalance_of_counts (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (j : ZMod n) (h : outerCount n k j < innerCount n k j) :
    ¬ LDB (GP n k) (f n k j+1) := by
  apply not_LDB_of_imbalance hk hn j
  rw [cancellation hk hn]
  omega

end Petersen
```

### `PetersenOuterSum.lean`

```lean
import PetersenPulses
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval

namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

omit [NeZero n] in
theorem intCast_injective_strip {m : ℕ} (hm : 2*m < n) {a b : ℤ}
    (ha : |a| ≤ m) (hb : |b| ≤ m) (he : (a : ZMod n) = (b : ZMod n)) : a = b := by
  have hz : ((a-b : ℤ) : ZMod n) = 0 := by push_cast; rw [he]; simp
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hab : |a-b| < (n : ℤ) := by
    have ht := abs_sub a b
    have hmn : (2 : ℤ)*m < n := by exact_mod_cast hm
    omega
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (Int.ofNat_lt.mp (by simpa only [Int.natCast_natAbs, Int.natAbs_natCast] using hab))
  omega

theorem p_intCast_strip {m : ℕ} (hm : 2*m < n) (z : ℤ) (hz : |z| ≤ m) :
    p n (z : ZMod n) = z.natAbs := by
  obtain ⟨a, ha, hlen⟩ := (outer_min (z : ZMod n)).1
  have hp := (outer_min (z : ZMod n)).2 z rfl
  have hab : |a| ≤ m := by
    have hpz : (p n (z : ZMod n) : ℤ) ≤ |z| := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hp)
    have hla : |a| = (p n (z : ZMod n) : ℤ) := by simpa only [Int.natCast_natAbs] using congrArg (fun t : ℕ => (t : ℤ)) hlen
    omega
  have he := intCast_injective_strip hm hab hz ha
  simpa [he] using hlen.symm

/-- A full cyclic sum supported on a short strip is exactly an integer interval sum. -/
theorem sum_short_strip (m : ℕ) (hm : 2*m < n) (g : ZMod n → ℤ)
    (hg : ∀ i, m < p n i → g i = 0) :
    (∑ i : ZMod n, g i) = ∑ z ∈ Finset.Icc (-(m : ℤ)) m, g (z : ZMod n) := by
  classical
  have hs : (∑ z ∈ Finset.Icc (-(m : ℤ)) m, g (z : ZMod n)) =
      ∑ i ∈ Finset.univ.filter (fun i => p n i ≤ m), g i := by
    apply Finset.sum_bij (fun (z : ℤ) _ => (z : ZMod n))
    · intro z hz
      have hz' : |z| ≤ (m : ℤ) := by simpa only [Finset.mem_Icc, abs_le] using hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [p_intCast_strip hm z hz']
      exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hz')
    · intro a ha b hb he
      apply intCast_injective_strip hm _ _ he
      · simpa only [Finset.mem_Icc, abs_le] using ha
      · simpa only [Finset.mem_Icc, abs_le] using hb
    · intro i hi
      have hip : p n i ≤ m := (Finset.mem_filter.mp hi).2
      obtain ⟨a, ha, hlen⟩ := (outer_min i).1
      refine ⟨a, ?_, ha⟩
      have hab : |a| ≤ (m : ℤ) := by
        have hh : (a.natAbs : ℤ) ≤ m := by exact_mod_cast (hlen ▸ hip : a.natAbs ≤ m)
        simpa only [Int.natCast_natAbs] using hh
      simpa only [Finset.mem_Icc, abs_le] using hab
    · intro _ _; rfl
  rw [hs]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  apply hg
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi

/-- Exact full outer count in the arithmetic strip; no graph term is omitted. -/
theorem outerCount_strip (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) :
    outerCount n k j =
      ∑ z ∈ Finset.Icc (-((k/2+1 : ℕ) : ℤ)) (k/2+1 : ℕ),
        pulse z.natAbs (H k z.natAbs+2) (f n k ((z : ZMod n)-j)+1) := by
  have hm : 2*(k/2+1) < n := by
    have hd := Nat.mod_add_div k 2
    have hr := Nat.mod_lt k (by decide : 0 < 2)
    have hm' : 2*(k/2+1) ≤ k+2 := by omega
    nlinarith
  rw [outerCount_sum, sum_short_strip (k/2+1) hm _ (outerPulse_vanish hk hn j)]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : |z| ≤ ((k/2+1 : ℕ) : ℤ) := by
    simpa only [Finset.mem_Icc, abs_le] using hz
  have hp := p_intCast_strip hm z hz'
  have hval := outer_shortcut_values hk hn (z : ZMod n) (by
    rw [hp]; exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hz'))
  simp only [outerPulse, hval.1, hval.2, hp ]

end Petersen
```

### `PetersenInnerArithmetic.lean`

```lean
import PetersenPulses

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem lineCost_block (hk : 0 < k) (a b : ℕ) (hb : b < k) :
    lineCost k (a*k+b) = a+H k b := by
  have hd : (a*k+b)/k = a := by
    rw [add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hb, zero_add]
  simp [lineCost, hd, Nat.add_mod, Nat.mod_eq_of_lt hb]

/-- Exact circulant profile on either inner ray, including its cyclic endpoint. -/
theorem f_inner_multiple (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (t : ℕ) (ht : t ≤ n/k) :
    f n k ((k*t : ℕ) : ZMod n) = min t (n/k-t+H k (n%k)) := by
  have hk0 : 0 < k := by omega
  have hr := Nat.mod_lt n hk0
  have hde := Nat.div_add_mod n k
  have htkn : k*t ≤ n := (Nat.mul_le_mul_left k ht).trans (by omega)
  by_cases he : k*t = n
  · have hdiv : n/k = t := by rw [← he]; simp [Nat.ne_of_gt hk0]
    have hmod : n%k = 0 := by rw [← he]; simp
    simp [he, f_zero hk hn, hdiv, hmod, H]
  · have hval : (((k*t : ℕ) : ZMod n)).val = k*t := ZMod.val_natCast_of_lt (by omega)
    have heq : n-k*t = (n/k-t)*k+n%k := by
      have hq : n/k-t+t = n/k := Nat.sub_add_cancel ht
      have hm : (n/k-t)*k+t*k = (n/k)*k := by rw [← Nat.add_mul, hq]
      nlinarith only [hm, hde, Nat.sub_add_cancel htkn]
    unfold f
    have hl : lineCost k (k*t) = t := by
      simpa [H, mul_comm] using lineCost_block hk0 t 0 (by omega)
    rw [hval, heq, hl, lineCost_block hk0 _ _ hr]

/-- All t up to half the sum of ray costs give full inner deficits. -/
theorem f_inner_full (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (t : ℕ)
    (ht : t ≤ n/k) (hT : 2*t ≤ n/k+H k (n%k)) :
    f n k ((k*t : ℕ) : ZMod n) = t := by
  rw [f_inner_multiple hk hn t ht, min_eq_left]
  omega

/-- Subtracting an inner route from a two-block decomposition computes the cross profile. -/
theorem f_cross_blocks (hk : 0 < k) (A B Ap Bp t : ℕ)
    (hB : B < k) (hBp : Bp < k) (ht : t ≤ A)
    (hj : A*k+B < n) (hsum : n = (A*k+B)+(Ap*k+Bp)) :
    f n k ((((A*k+B : ℕ) : ZMod n))-(k : ZMod n)*(t : ZMod n)) =
      min (A-t+H k B) (Ap+t+H k Bp) := by
  have hjt : (A-t)*k+B < n := by
    have hA : A-t ≤ A := Nat.sub_le _ _
    have hm := Nat.mul_le_mul_right k hA
    omega
  have he : (((A*k+B : ℕ) : ZMod n))-(k : ZMod n)*(t : ZMod n) =
      (((A-t)*k+B : ℕ) : ZMod n) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub ht]
    ring
  rw [he]
  unfold f
  rw [ZMod.val_natCast_of_lt hjt]
  have hrest : n-((A-t)*k+B) = (Ap+t)*k+Bp := by
    have hA : (A-t)*k+t*k = A*k := by rw [← Nat.add_mul, Nat.sub_add_cancel ht]
    have hle : (A-t)*k+B ≤ n := by omega
    have hsub := Nat.sub_add_cancel hle
    nlinarith only [hA, hsum, hsub]
  rw [hrest, lineCost_block hk _ _ hB, lineCost_block hk _ _ hBp]

end Petersen
```

### `PetersenSelectedRoots.lean`

```lean
import PetersenPulses

namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The one even root or the two adjacent odd roots. -/
def roots (C : ℤ) : Finset ℤ := if C%2 = 0 then {C/2} else {C/2, C/2+1}

theorem root_bounds (C t : ℤ) (hC : 2 ≤ C) (ht : t ∈ roots C) :
    1 ≤ t ∧ t ≤ (C+1)/2 ∧ -1 ≤ C-2*t ∧ C-2*t ≤ 1 := by
  simp only [roots] at ht
  split_ifs at ht <;> simp only [Finset.mem_singleton, Finset.mem_insert] at ht <;> omega

theorem root_weight (C Cp : ℤ) (hp : 2 ≤ Cp) :
    ∑ t ∈ roots C, K (min (C-t) (Cp+t)-t) = 2 := by
  unfold roots
  split_ifs with h
  · simp only [Finset.sum_singleton, K]
    split_ifs <;> omega
  · have he : C/2 ≠ C/2+1 := by omega
    rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using he : C/2 ∉ ({C/2+1} : Finset ℤ)), Finset.sum_singleton]
    simp only [K]
    split_ifs <;> omega

/-- The signed route indices used by the two groups of roots. -/
def rootIndex (C Cp : ℤ) : (↥(roots C) ⊕ ↥(roots Cp)) → ZMod n
  | Sum.inl t => (k : ZMod n)*(t.val : ZMod n)
  | Sum.inr t => (k : ZMod n)*((-t.val : ℤ) : ZMod n)

/-- Four inner units in the *actual* count, assuming only the selected f-values
and injectivity of the chosen routes. -/
theorem innerCount_four_roots (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (j : ZMod n) (C Cp : ℤ) (hC : 2 ≤ C) (hp : 2 ≤ Cp)
    (hinj : Function.Injective (rootIndex (n := n) (k := k) C Cp))
    (hfull : ∀ t ∈ roots C, f n k ((k : ZMod n)*(t : ZMod n)) = t.natAbs)
    (hfullp : ∀ t ∈ roots Cp, f n k ((k : ZMod n)*((-t : ℤ) : ZMod n)) = (-t).natAbs)
    (hcross : ∀ t ∈ roots C,
      (f n k (j-(k : ZMod n)*(t : ZMod n)) : ℤ) = min (C-t) (Cp+t))
    (hcrossp : ∀ t ∈ roots Cp,
      (f n k (j-(k : ZMod n)*((-t : ℤ) : ZMod n)) : ℤ) = min (Cp-t) (C+t)) :
    4 ≤ innerCount n k j := by
  classical
  have hsel := innerCount_selected (k := k) j (rootIndex (k := k) C Cp) hinj
  have hlow : (4 : ℤ) ≤ ∑ a, innerPulse n k j (rootIndex (k := k) C Cp a) := by
    rw [Fintype.sum_sum_type]
    change 4 ≤ (∑ t : ↥(roots C), innerPulse n k j ((k : ZMod n)*(t.val : ZMod n))) +
      (∑ t : ↥(roots Cp), innerPulse n k j ((k : ZMod n)*((-t.val : ℤ) : ZMod n)))
    have hpos : (2 : ℤ) ≤ ∑ t : ↥(roots C), innerPulse n k j ((k : ZMod n)*(t.val : ZMod n)) := by
      rw [← root_weight C Cp hp, ← Finset.sum_coe_sort]
      apply Finset.sum_le_sum
      intro t _
      have hb := root_bounds C t.val hC t.property
      have he : (t.val.natAbs : ℤ) = t.val := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
      have h := innerPulse_route hk hn j t.val (hfull t.val t.property)
      rw [hcross t.val t.property, he] at h
      exact h
    have hneg : (2 : ℤ) ≤ ∑ t : ↥(roots Cp), innerPulse n k j ((k : ZMod n)*((-t.val : ℤ) : ZMod n)) := by
      rw [← root_weight Cp C hC, ← Finset.sum_coe_sort]
      apply Finset.sum_le_sum
      intro t _
      have hb := root_bounds Cp t.val hp t.property
      have he : ((-t.val).natAbs : ℤ) = t.val := by rw [Int.natCast_natAbs, abs_neg, abs_of_nonneg (by omega)]
      have h := innerPulse_route hk hn j (-t.val) (hfullp t.val t.property)
      rw [hcrossp t.val t.property, he] at h
      exact h
    omega
  omega

def rootRoute (C Cp : ℤ) : (↥(roots C) ⊕ ↥(roots Cp)) → ℤ
  | Sum.inl t => t.val
  | Sum.inr t => -t.val

theorem rootRoute_bounds (C Cp : ℤ) (hC : 2 ≤ C) (hp : 2 ≤ Cp)
    (a : ↥(roots C) ⊕ ↥(roots Cp)) :
    -((Cp+1)/2) ≤ rootRoute C Cp a ∧ rootRoute C Cp a ≤ (C+1)/2 := by
  have hCpos : 1 ≤ (C+1)/2 := by omega
  have hppos : 1 ≤ (Cp+1)/2 := by omega
  cases a with
  | inl t => have ht := root_bounds C t.val hC t.property; dsimp [rootRoute]; omega
  | inr t => have ht := root_bounds Cp t.val hp t.property; dsimp [rootRoute]; omega

theorem rootRoute_injective (C Cp : ℤ) (hC : 2 ≤ C) (hp : 2 ≤ Cp) :
    Function.Injective (rootRoute C Cp) := by
  intro a b he
  cases a with
  | inl t =>
    cases b with
    | inl u => exact congrArg Sum.inl (Subtype.ext he)
    | inr u =>
      have ht := root_bounds C t.val hC t.property
      have hu := root_bounds Cp u.val hp u.property
      dsimp [rootRoute] at he
      omega
  | inr t =>
    cases b with
    | inl u =>
      have ht := root_bounds Cp t.val hp t.property
      have hu := root_bounds C u.val hC u.property
      dsimp [rootRoute] at he
      omega
    | inr u =>
      apply congrArg Sum.inr
      apply Subtype.ext
      dsimp [rootRoute] at he
      omega

omit [NeZero n] in
/-- This single width condition proves both within-ray injectivity and ray disjointness. -/
theorem rootIndex_injective (hk : 2 ≤ k) (C Cp : ℤ) (hC : 2 ≤ C) (hp : 2 ≤ Cp)
    (hwidth : (k : ℤ)*((C+1)/2+(Cp+1)/2) < n) :
    Function.Injective (rootIndex (n := n) (k := k) C Cp) := by
  intro a b he
  have ha := rootRoute_bounds C Cp hC hp a
  have hb := rootRoute_bounds C Cp hC hp b
  have hd : |rootRoute C Cp a-rootRoute C Cp b| ≤ (C+1)/2+(Cp+1)/2 := by
    rw [abs_le]; omega
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ (k : ℤ) by omega)
  have hab : |(k : ℤ)*rootRoute C Cp a-(k : ℤ)*rootRoute C Cp b| < n := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ (k : ℤ) by omega)]
    omega
  have hi (x : ↥(roots C) ⊕ ↥(roots Cp)) :
      (((k : ℤ)*rootRoute C Cp x : ℤ) : ZMod n) = rootIndex (k := k) C Cp x := by
    cases x <;> simp [rootRoute, rootIndex, Int.cast_mul]
  have hz : (((k : ℤ)*rootRoute C Cp a-(k : ℤ)*rootRoute C Cp b : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_sub, hi, hi, he, sub_self]
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    (Int.ofNat_lt.mp (by simpa only [Int.natCast_natAbs, Int.natAbs_natCast] using hab))
  apply rootRoute_injective C Cp hC hp
  have hk0 : (0 : ℤ) < k := by omega
  nlinarith

end Petersen
```

### `PetersenInnerWitness.lean`

```lean
import PetersenInnerArithmetic
import Mathlib.Tactic.LinearCombination
import PetersenSelectedRoots

namespace Petersen
variable {n k : ℕ} [NeZero n]

private theorem root_nat (C : ℕ) (hC : 2 ≤ C) (t : ℤ) (ht : t ∈ roots C) :
    (t.natAbs : ℤ) = t := by
  have hb := root_bounds C t (by exact_mod_cast hC) ht
  rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]

private theorem root_full (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (C : ℕ) (hC : 2 ≤ C) (hT : C ≤ 2*((n/k+H k (n%k))/2))
    (t : ℤ) (ht : t ∈ roots C) :
    f n k ((k : ZMod n)*(t : ZMod n)) = t.natAbs := by
  have hb := root_bounds C t (by exact_mod_cast hC) ht
  have hnat := root_nat C hC t ht
  have hq : k+2 ≤ n/k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by nlinarith)
  have hH : H k (n%k) ≤ k+1 := by unfold H; omega
  have hdt := Nat.mod_add_div (n/k+H k (n%k)) 2
  have hTq : (n/k+H k (n%k))/2 ≤ n/k := by omega
  have htn : t.natAbs ≤ n/k := by omega
  have htT : 2*t.natAbs ≤ n/k+H k (n%k) := by omega
  have hf := f_inner_full hk hn t.natAbs htn htT
  have he : ((t.natAbs : ℕ) : ZMod n) = (t : ZMod n) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod n)) hnat
  simpa only [Nat.cast_mul, he] using hf

private theorem root_axis (A B C : ℕ) (hC : 2 ≤ C) (hc : C = A+H k B)
    (haxis : H k B ≤ A) (t : ℤ) (ht : t ∈ roots C) : t.natAbs ≤ A := by
  have hb := root_bounds C t (by exact_mod_cast hC) ht
  have hnat := root_nat C hC t ht
  omega

private theorem root_cross (hk : 0 < k) (A B Ap Bp C Cp : ℕ)
    (hB : B < k) (hBp : Bp < k) (hC : 2 ≤ C)
    (hc : C = A+H k B) (hcp : Cp = Ap+H k Bp) (haxis : H k B ≤ A)
    (hj : A*k+B < n) (hsum : n = (A*k+B)+(Ap*k+Bp))
    (t : ℤ) (ht : t ∈ roots C) :
    (f n k ((((A*k+B : ℕ) : ZMod n))-(k : ZMod n)*(t : ZMod n)) : ℤ) =
      min ((C : ℤ)-t) ((Cp : ℤ)+t) := by
  have hnat := root_nat C hC t ht
  have hta := root_axis A B C hC hc haxis t ht
  have he : ((t.natAbs : ℕ) : ZMod n) = (t : ZMod n) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod n)) hnat
  rw [← he, f_cross_blocks hk A B Ap Bp t.natAbs hB hBp hta hj hsum]
  rw [Nat.cast_min, Nat.cast_add, Nat.cast_sub hta, Nat.cast_add, hc, hcp]
  push_cast
  have htAbs : |t| = t := by simpa only [Int.natCast_natAbs] using hnat
  rw [htAbs]
  congr 1 <;> ring

/-- The four-inner-unit theorem with all distance/profile premises discharged by arithmetic
on a two-block decomposition. The same interface serves every low/high witness class. -/
theorem innerCount_four_blocks (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (A B Ap Bp C Cp : ℕ) (hB : B < k) (hBp : Bp < k)
    (hc : C = A+H k B) (hcp : Cp = Ap+H k Bp) (hC : 2 ≤ C) (hCp : 2 ≤ Cp)
    (haxis : H k B ≤ A) (haxisp : H k Bp ≤ Ap)
    (hj : A*k+B < n) (hjp : Ap*k+Bp < n)
    (hsum : n = (A*k+B)+(Ap*k+Bp))
    (hT : C ≤ 2*((n/k+H k (n%k))/2)) (hTp : Cp ≤ 2*((n/k+H k (n%k))/2))
    (hwidth : (k : ℤ)*(((C : ℤ)+1)/2+((Cp : ℤ)+1)/2) < n) :
    4 ≤ innerCount n k (((A*k+B : ℕ) : ZMod n)) := by
  have hCi : (2 : ℤ) ≤ C := by exact_mod_cast hC
  have hCpi : (2 : ℤ) ≤ Cp := by exact_mod_cast hCp
  apply innerCount_four_roots hk hn _ C Cp hCi hCpi (rootIndex_injective hk _ _ hCi hCpi hwidth)
  · exact root_full hk hn C hC hT
  · intro t ht
    have hf := root_full hk hn Cp hCp hTp t ht
    have he : (k : ZMod n)*((-t : ℤ) : ZMod n) = -((k : ZMod n)*(t : ZMod n)) := by push_cast; ring
    rw [he, f_neg hk hn, hf, Int.natAbs_neg]
  · exact root_cross (by omega) A B Ap Bp C Cp hB hBp hC hc hcp haxis hj hsum
  · intro t ht
    have hsum' : n = (Ap*k+Bp)+(A*k+B) := by omega
    have hx := root_cross (n := n) (by omega : 0 < k) Ap Bp A B Cp C
      hBp hB hCp hcp hc haxisp hjp hsum' t ht
    have he : (((A*k+B : ℕ) : ZMod n))-(k : ZMod n)*((-t : ℤ) : ZMod n) =
        -((((Ap*k+Bp : ℕ) : ZMod n))-(k : ZMod n)*(t : ZMod n)) := by
      have hncast : (((A*k+B)+(Ap*k+Bp) : ℕ) : ZMod n) = 0 := by rw [← hsum]; exact ZMod.natCast_self n
      push_cast at hncast ⊢
      linear_combination hncast
    rw [he, f_neg hk hn]
    exact hx

end Petersen
```

### `PetersenLowInner.lean`

```lean
import PetersenInnerWitness

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- All low radii share the same inner counting argument. -/
theorem low_inner (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (a : ℕ)
    (ha : 2 ≤ a) (haq : a ≤ (n/k)/2) :
    f n k (((a*k : ℕ) : ZMod n)) = a ∧
      4 ≤ innerCount n k (((a*k : ℕ) : ZMod n)) := by
  have hk0 : 0 < k := by omega
  have hq : k+2 ≤ n/k := (Nat.le_div_iff_mul_le hk0).mpr (by nlinarith)
  have hr := Nat.mod_lt n hk0
  have hd := Nat.div_add_mod n k
  have hH : 2*H k (n%k) ≤ k+1 := by unfold H; omega
  have hHq : H k (n%k) ≤ n/k-a := by omega
  have haqn : a ≤ n/k := by omega
  have hrem : n/k-a+a = n/k := Nat.sub_add_cancel haqn
  have hmul : (n/k-a)*k+a*k = (n/k)*k := by rw [← Nat.add_mul, hrem]
  have hs : n = (a*k+0)+((n/k-a)*k+n%k) := by nlinarith only [hmul, hd]
  have hj : a*k+0 < n := by
    have hm := Nat.mul_le_mul_right k (show a+1 ≤ n/k by omega)
    have hqkn : n/k*k ≤ n := Nat.div_mul_le_self n k
    have hmk : a*k < (a+1)*k := Nat.mul_lt_mul_of_pos_right (by omega) hk0
    exact lt_of_lt_of_le hmk (hm.trans hqkn)
  have hjp : (n/k-a)*k+n%k < n := by nlinarith [hs]
  have hC : a ≤ 2*((n/k+H k (n%k))/2) := by omega
  have hCp : n/k-a+H k (n%k) ≤ 2*((n/k+H k (n%k))/2) := by omega
  have hwidth : (k : ℤ)*(((a : ℤ)+1)/2+(((n/k-a+H k (n%k) : ℕ) : ℤ)+1)/2) < n := by
    have hi : ((a : ℤ)+1)/2+(((n/k-a+H k (n%k) : ℕ) : ℤ)+1)/2 < n/k := by
      omega
    have hqi : (k : ℤ)*(n/k : ℕ) ≤ n := by exact_mod_cast (by omega : k*(n/k) ≤ n)
    have hm := mul_lt_mul_of_pos_left hi (show (0 : ℤ) < k by omega)
    exact lt_of_lt_of_le hm hqi
  constructor
  · rw [mul_comm a k, f_inner_multiple (by omega) hn a haqn, min_eq_left (by omega)]
  · have h := innerCount_four_blocks (by omega : 2 ≤ k) hn a 0 (n/k-a) (n%k)
      a (n/k-a+H k (n%k)) (by omega) hr (by simp [H]) rfl ha (by omega)
      (by simp [H]) hHq hj hjp hs hC hCp hwidth
    simpa only [add_zero] using h

end Petersen
```

### `PetersenUTableDefs.lean`

```lean
import PetersenPulses

namespace PetersenTables
def sgn (x : Int) : Int := if 0 < x then 1 else if x < 0 then -1 else 0

def localG (k x : Int) : Int :=
  if x < -k then -x-k-1
  else if x < 0 then min (-x) (k+x-1)
  else if x < k then min x (k+1-x)
  else 1+min (x-k) (2*k+1-x)

def pulse (a b c : Int) : Int := sgn (c-a) - sgn (c-b)

def term (h kp C z t e : Int) : Int :=
  pulse t (min t (2*h+kp+1-t)+2) (1+C+localG (2*h+kp) (z+e*t))

def U (h kp C z : Int) : Int :=
  term h kp C z (h-1) (-1) + term h kp C z (h-1) 1 +
  term h kp C z h (-1) + term h kp C z h 1 +
  term h kp C z (h+1) (-1) + term h kp C z (h+1) 1

theorem sgn_eq_sign (x : ℤ) : sgn x = Petersen.sign x := by
  unfold sgn Petersen.sign
  split_ifs <;> omega

theorem pulse_eq (a b c : ℤ) : pulse a b c = Petersen.pulse a b c := by
  simp only [pulse, Petersen.pulse, sgn_eq_sign]
end PetersenTables
```

### `PetersenUTablesPositive.lean`

```lean
import PetersenUTableDefs

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
namespace PetersenTables

theorem even_pos_low_0 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_low_1 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_low_2 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    term h 0 C z h (-1) = (if z = h then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_low_3 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_low_4 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    term h 0 C z (h+1) (-1) = (if z = h+1 then 1 else 0) + (if h = 2 ∧ z = 0 then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_low_5 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_low (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : C = h+1) :
    U h 0 C z = (if z = h then 1 else 0) + (if z = h+1 then 1 else 0) + (if h = 2 ∧ z = 0 then 1 else 0) + (if h = 1 ∧ z = 0 then 2 else 0) := by
  dsimp only [U]
  rw [even_pos_low_0 h z C hh hz hzk hc, even_pos_low_1 h z C hh hz hzk hc, even_pos_low_2 h z C hh hz hzk hc, even_pos_low_3 h z C hh hz hzk hc, even_pos_low_4 h z C hh hz hzk hc, even_pos_low_5 h z C hh hz hzk hc]
  omega

theorem even_pos_high_0 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_high_1 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_high_2 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    term h 0 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_high_3 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_high_4 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    term h 0 C z (h+1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_high_5 (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_pos_high (h z C : Int) (hh : 2 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+0) (hc : h+2 ≤ C) :
    U h 0 C z = 0 := by
  dsimp only [U]
  rw [even_pos_high_0 h z C hh hz hzk hc, even_pos_high_1 h z C hh hz hzk hc, even_pos_high_2 h z C hh hz hzk hc, even_pos_high_3 h z C hh hz hzk hc, even_pos_high_4 h z C hh hz hzk hc, even_pos_high_5 h z C hh hz hzk hc]
  omega

theorem odd_pos_low_0 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_low_1 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_low_2 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    term h 1 C z h (-1) = (if z = h then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_low_3 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_low_4 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    term h 1 C z (h+1) (-1) = (if z = h then 1 else 0) + (if z = h+1 then 2 else 0) + (if z = h+2 then 1 else 0) + (if h = 2 ∧ z = 0 then 1 else 0) + (if h = 1 ∧ z = 0 then 2 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_low_5 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    term h 1 C z (h+1) 1 = (if z = h then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_low (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+1) :
    U h 1 C z = (if z = h then 3 else 0) + (if z = h+1 then 2 else 0) + (if z = h+2 then 1 else 0) + (if h = 2 ∧ z = 0 then 1 else 0) + (if h = 1 ∧ z = 0 then 2 else 0) := by
  dsimp only [U]
  rw [odd_pos_low_0 h z C hh hz hzk hc, odd_pos_low_1 h z C hh hz hzk hc, odd_pos_low_2 h z C hh hz hzk hc, odd_pos_low_3 h z C hh hz hzk hc, odd_pos_low_4 h z C hh hz hzk hc, odd_pos_low_5 h z C hh hz hzk hc]
  omega

theorem odd_pos_middle_0 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_middle_1 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_middle_2 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_middle_3 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_middle_4 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    term h 1 C z (h+1) (-1) = (if z = h+1 then 1 else 0) + (if h = 1 ∧ z = 0 then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_middle_5 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_middle (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : C = h+2) :
    U h 1 C z = (if z = h+1 then 1 else 0) + (if h = 1 ∧ z = 0 then 1 else 0) := by
  dsimp only [U]
  rw [odd_pos_middle_0 h z C hh hz hzk hc, odd_pos_middle_1 h z C hh hz hzk hc, odd_pos_middle_2 h z C hh hz hzk hc, odd_pos_middle_3 h z C hh hz hzk hc, odd_pos_middle_4 h z C hh hz hzk hc, odd_pos_middle_5 h z C hh hz hzk hc]
  omega

theorem odd_pos_high_0 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_high_1 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_high_2 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_high_3 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_high_4 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    term h 1 C z (h+1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_high_5 (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_pos_high (h z C : Int) (hh : 1 ≤ h) (hz : 0 ≤ z) (hzk : z < 2*h+1) (hc : h+3 ≤ C) :
    U h 1 C z = 0 := by
  dsimp only [U]
  rw [odd_pos_high_0 h z C hh hz hzk hc, odd_pos_high_1 h z C hh hz hzk hc, odd_pos_high_2 h z C hh hz hzk hc, odd_pos_high_3 h z C hh hz hzk hc, odd_pos_high_4 h z C hh hz hzk hc, odd_pos_high_5 h z C hh hz hzk hc]
  omega


end PetersenTables
```

### `PetersenUTablesNegative.lean`

```lean
import PetersenUTableDefs

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
namespace PetersenTables

theorem even_neg_low_0 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_low_1 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_low_2 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    term h 0 C z h (-1) = (if z = -(h-1) then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_low_3 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_low_4 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    term h 0 C z (h+1) (-1) = (if z = -(h-2) then 1 else 0) + (if z = -(h-1) then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_low_5 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_low (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h-1) ≤ z) (hc : C = h+1) :
    U h 0 C z = (if z = -(h-2) then 1 else 0) + (if z = -(h-1) then 2 else 0) := by
  dsimp only [U]
  rw [even_neg_low_0 h z C hh hz hzk hc, even_neg_low_1 h z C hh hz hzk hc, even_neg_low_2 h z C hh hz hzk hc, even_neg_low_3 h z C hh hz hzk hc, even_neg_low_4 h z C hh hz hzk hc, even_neg_low_5 h z C hh hz hzk hc]
  omega

theorem even_neg_middle_0 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_middle_1 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_middle_2 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 0 C z h (-1) = (if z = -h then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_middle_3 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_middle_4 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 0 C z (h+1) (-1) = (if z = -(h-1) then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_middle_5 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_middle (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    U h 0 C z = (if z = -(h-1) then 1 else 0) + (if z = -h then 1 else 0) := by
  dsimp only [U]
  rw [even_neg_middle_0 h z C hh hz hzk hc, even_neg_middle_1 h z C hh hz hzk hc, even_neg_middle_2 h z C hh hz hzk hc, even_neg_middle_3 h z C hh hz hzk hc, even_neg_middle_4 h z C hh hz hzk hc, even_neg_middle_5 h z C hh hz hzk hc]
  omega

theorem even_neg_high_0 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_high_1 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_high_2 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    term h 0 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_high_3 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_high_4 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    term h 0 C z (h+1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_high_5 (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem even_neg_high (h z C : Int) (hh : 2 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+3 ≤ C) :
    U h 0 C z = 0 := by
  dsimp only [U]
  rw [even_neg_high_0 h z C hh hz hzk hc, even_neg_high_1 h z C hh hz hzk hc, even_neg_high_2 h z C hh hz hzk hc, even_neg_high_3 h z C hh hz hzk hc, even_neg_high_4 h z C hh hz hzk hc, even_neg_high_5 h z C hh hz hzk hc]
  omega

theorem odd_neg_low_0 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_low_1 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_low_2 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_low_3 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_low_4 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 1 C z (h+1) (-1) = (if z = -(h-1) then 1 else 0) + (if z = -h then 2 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_low_5 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_low (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+2) :
    U h 1 C z = (if z = -(h-1) then 1 else 0) + (if z = -h then 2 else 0) := by
  dsimp only [U]
  rw [odd_neg_low_0 h z C hh hz hzk hc, odd_neg_low_1 h z C hh hz hzk hc, odd_neg_low_2 h z C hh hz hzk hc, odd_neg_low_3 h z C hh hz hzk hc, odd_neg_low_4 h z C hh hz hzk hc, odd_neg_low_5 h z C hh hz hzk hc]
  omega

theorem odd_neg_middle_0 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_middle_1 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_middle_2 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_middle_3 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_middle_4 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    term h 1 C z (h+1) (-1) = (if z = -h then 1 else 0) := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_middle_5 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_middle (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : C = h+3) :
    U h 1 C z = (if z = -h then 1 else 0) := by
  dsimp only [U]
  rw [odd_neg_middle_0 h z C hh hz hzk hc, odd_neg_middle_1 h z C hh hz hzk hc, odd_neg_middle_2 h z C hh hz hzk hc, odd_neg_middle_3 h z C hh hz hzk hc, odd_neg_middle_4 h z C hh hz hzk hc, odd_neg_middle_5 h z C hh hz hzk hc]
  omega

theorem odd_neg_high_0 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_high_1 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_high_2 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_high_3 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_high_4 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    term h 1 C z (h+1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_high_5 (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem odd_neg_high (h z C : Int) (hh : 1 ≤ h) (hz : z ≤ -1) (hzk : -(h) ≤ z) (hc : h+4 ≤ C) :
    U h 1 C z = 0 := by
  dsimp only [U]
  rw [odd_neg_high_0 h z C hh hz hzk hc, odd_neg_high_1 h z C hh hz hzk hc, odd_neg_high_2 h z C hh hz hzk hc, odd_neg_high_3 h z C hh hz hzk hc, odd_neg_high_4 h z C hh hz hzk hc, odd_neg_high_5 h z C hh hz hzk hc]
  omega


end PetersenTables
```

### `PetersenUTablesPrimary.lean`

```lean
import PetersenUTableDefs

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.unusedVariables false
namespace PetersenTables

theorem primary_0_2_0 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_2_1 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_2_2 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 0 C z h (-1) = 1 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_2_3 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_2_4 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 0 C z (h+1) (-1) = 1 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_2_5 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_2 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 2) :
    U h 0 C z = 2 := by
  dsimp only [U]
  rw [primary_0_2_0 h z C hh hz hc, primary_0_2_1 h z C hh hz hc, primary_0_2_2 h z C hh hz hc, primary_0_2_3 h z C hh hz hc, primary_0_2_4 h z C hh hz hc, primary_0_2_5 h z C hh hz hc]
  omega

theorem primary_0_3_0 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_3_1 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_3_2 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 0 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_3_3 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_3_4 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 0 C z (h+1) (-1) = 1 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_3_5 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_3 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : C = 3) :
    U h 0 C z = 1 := by
  dsimp only [U]
  rw [primary_0_3_0 h z C hh hz hc, primary_0_3_1 h z C hh hz hc, primary_0_3_2 h z C hh hz hc, primary_0_3_3 h z C hh hz hc, primary_0_3_4 h z C hh hz hc, primary_0_3_5 h z C hh hz hc]
  omega

theorem primary_0_high_0 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 0 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_high_1 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 0 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_high_2 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 0 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_high_3 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 0 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_high_4 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 0 C z (h+1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_high_5 (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 0 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_0_high (h z C : Int) (hh : 2 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    U h 0 C z = 0 := by
  dsimp only [U]
  rw [primary_0_high_0 h z C hh hz hc, primary_0_high_1 h z C hh hz hc, primary_0_high_2 h z C hh hz hc, primary_0_high_3 h z C hh hz hc, primary_0_high_4 h z C hh hz hc, primary_0_high_5 h z C hh hz hc]
  omega

theorem primary_1_2_0 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_2_1 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_2_2 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_2_3 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_2_4 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 1 C z (h+1) (-1) = 2 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_2_5 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_2 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 2) :
    U h 1 C z = 2 := by
  dsimp only [U]
  rw [primary_1_2_0 h z C hh hz hc, primary_1_2_1 h z C hh hz hc, primary_1_2_2 h z C hh hz hc, primary_1_2_3 h z C hh hz hc, primary_1_2_4 h z C hh hz hc, primary_1_2_5 h z C hh hz hc]
  omega

theorem primary_1_3_0 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_3_1 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_3_2 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_3_3 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_3_4 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 1 C z (h+1) (-1) = 1 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_3_5 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_3 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : C = 3) :
    U h 1 C z = 1 := by
  dsimp only [U]
  rw [primary_1_3_0 h z C hh hz hc, primary_1_3_1 h z C hh hz hc, primary_1_3_2 h z C hh hz hc, primary_1_3_3 h z C hh hz hc, primary_1_3_4 h z C hh hz hc, primary_1_3_5 h z C hh hz hc]
  omega

theorem primary_1_high_0 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 1 C z (h-1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_high_1 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 1 C z (h-1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_high_2 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 1 C z h (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_high_3 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 1 C z h 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_high_4 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 1 C z (h+1) (-1) = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_high_5 (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    term h 1 C z (h+1) 1 = 0 := by
  dsimp only [term, pulse, sgn, localG]
  omega

theorem primary_1_high (h z C : Int) (hh : 1 ≤ h) (hz : z = 0) (hc : 4 ≤ C) :
    U h 1 C z = 0 := by
  dsimp only [U]
  rw [primary_1_high_0 h z C hh hz hc, primary_1_high_1 h z C hh hz hc, primary_1_high_2 h z C hh hz hc, primary_1_high_3 h z C hh hz hc, primary_1_high_4 h z C hh hz hc, primary_1_high_5 h z C hh hz hc]
  omega


end PetersenTables
```

### `PetersenUTableBounds.lean`

```lean
import PetersenUTablesPositive
import PetersenUTablesNegative
import PetersenUTablesPrimary
set_option Elab.async false
set_option maxHeartbeats 200000
namespace PetersenTables

theorem even_pos_le_one (h z C : Int) (hh : 2 ≤ h)
    (hz : 0 ≤ z) (hzk : z < 2*h) (hC : h+1 ≤ C) : U h 0 C z ≤ 1 := by
  by_cases hc : C = h+1
  · rw [even_pos_low h z C hh hz (by omega) hc]
    omega
  · have hc2 : h+2 ≤ C := by omega
    rw [even_pos_high h z C hh hz (by omega) hc2]
    omega


theorem odd_pos_le_one (h z C : Int) (hh : 1 ≤ h)
    (hz : 0 ≤ z) (hzk : z < 2*h+1) (hC : h+2 ≤ C) : U h 1 C z ≤ 1 := by
  by_cases hc : C = h+2
  · rw [odd_pos_middle h z C hh hz (by omega) hc]
    omega
  · have hc3 : h+3 ≤ C := by omega
    rw [odd_pos_high h z C hh hz hzk hc3]
    omega


theorem odd_pos_le_three (h z C : Int) (hh : 1 ≤ h)
    (hz : 0 ≤ z) (hzk : z < 2*h+1) (hC : h+1 ≤ C) : U h 1 C z ≤ 3 := by
  by_cases hc : C = h+1
  · rw [odd_pos_low h z C hh hz (by omega) hc]
    omega
  · have hc2 : h+2 ≤ C := by omega
    have hu := odd_pos_le_one h z C hh hz hzk hc2
    calc U h 1 C z ≤ 1 := hu
         _ ≤ 3 := by omega


theorem even_neg_le_two (h u C : Int) (hh : 2 ≤ h)
    (hu : 1 ≤ u) (huh : u ≤ h-1) (hC : h+1 ≤ C) : U h 0 C (-u) ≤ 2 := by
  have hz : -u ≤ -1 := by omega
  have hzk : -(h-1) ≤ -u := by omega
  by_cases hc : C = h+1
  · rw [even_neg_low h (-u) C hh hz hzk hc]
    omega
  · have hc2 : h+2 ≤ C := by omega
    by_cases hc' : C = h+2
    · have hzk' : -h ≤ -u := by omega
      rw [even_neg_middle h (-u) C hh hz hzk' hc']
      omega
    · have hc3 : h+3 ≤ C := by omega
      have hzk' : -h ≤ -u := by omega
      rw [even_neg_high h (-u) C hh hz hzk' hc3]
      omega


theorem even_neg_le_one (h u C : Int) (hh : 2 ≤ h)
    (hu : 1 ≤ u) (huh : u ≤ h) (hC : h+2 ≤ C) : U h 0 C (-u) ≤ 1 := by
  have hz : -u ≤ -1 := by omega
  have hzk : -h ≤ -u := by omega
  by_cases hc : C = h+2
  · rw [even_neg_middle h (-u) C hh hz hzk hc]
    omega
  · have hc3 : h+3 ≤ C := by omega
    rw [even_neg_high h (-u) C hh hz hzk hc3]
    omega


theorem odd_neg_le_two (h u C : Int) (hh : 1 ≤ h)
    (hu : 1 ≤ u) (huh : u ≤ h) (hC : h+2 ≤ C) : U h 1 C (-u) ≤ 2 := by
  have hz : -u ≤ -1 := by omega
  have hzk : -h ≤ -u := by omega
  by_cases hc : C = h+2
  · rw [odd_neg_low h (-u) C hh hz hzk hc]
    omega
  · have hc3 : h+3 ≤ C := by omega
    by_cases hc' : C = h+3
    · rw [odd_neg_middle h (-u) C hh hz hzk hc']
      omega
    · have hc4 : h+4 ≤ C := by omega
      rw [odd_neg_high h (-u) C hh hz hzk hc4]
      omega


theorem odd_neg_le_one (h u C : Int) (hh : 1 ≤ h)
    (hu : 1 ≤ u) (huh : u ≤ h) (hC : h+3 ≤ C) : U h 1 C (-u) ≤ 1 := by
  have hz : -u ≤ -1 := by omega
  have hzk : -h ≤ -u := by omega
  by_cases hc : C = h+3
  · rw [odd_neg_middle h (-u) C hh hz hzk hc]
    omega
  · have hc4 : h+4 ≤ C := by omega
    rw [odd_neg_high h (-u) C hh hz hzk hc4]
    omega


def normU (h kp C z : Int) : Int :=
  if z < 2*h+kp then U h kp C z else U h kp (C+1) (z-(2*h+kp))

theorem even_norm_pos_le_one (h z C : Int) (hh : 2 ≤ h)
    (hz : 0 ≤ z) (hzk : z < 4*h) (hC : h+1 ≤ C) : normU h 0 C z ≤ 1 := by
  simp only [normU, Int.add_zero]
  split
  next hlt => exact even_pos_le_one h z C hh hz hlt hC
  next hnlt =>
    have hz' : 0 ≤ z-2*h := by omega
    have hzk' : z-2*h < 2*h := by omega
    have hC' : h+1 ≤ C+1 := by omega
    exact even_pos_le_one h (z-2*h) (C+1) hh hz' hzk' hC'


theorem odd_norm_pos_le_one (h z C : Int) (hh : 1 ≤ h)
    (hz : 0 ≤ z) (hzk : z < 4*h+2) (hC : h+2 ≤ C) : normU h 1 C z ≤ 1 := by
  unfold normU
  split
  next hlt => exact odd_pos_le_one h z C hh hz hlt hC
  next hnlt =>
    have hz' : 0 ≤ z-(2*h+1) := by omega
    have hzk' : z-(2*h+1) < 2*h+1 := by omega
    have hC' : h+2 ≤ C+1 := by omega
    exact odd_pos_le_one h (z-(2*h+1)) (C+1) hh hz' hzk' hC'


theorem even_evenq_negative (h Q r s : Int) (hh : 2 ≤ h)
    (hQ : h+1 ≤ Q) (hr : 0 ≤ r) (hrk : r < 2*h)
    (hs : 1 ≤ s) (hsh : s ≤ h-1) :
    U h 0 Q (-s) + normU h 0 Q (r+s) ≤ 3 := by
  have h1 := even_neg_le_two h s Q hh hs hsh hQ
  have hz : 0 ≤ r+s := by omega
  have hzk : r+s < 4*h := by omega
  have h2 := even_norm_pos_le_one h (r+s) Q hh hz hzk hQ
  calc U h 0 Q (-s) + normU h 0 Q (r+s) ≤ 2+1 := Int.add_le_add h1 h2
       _ ≤ 3 := by omega


theorem odd_evenq_negative (h Q r s : Int) (hh : 1 ≤ h)
    (hQ : h+2 ≤ Q) (hr : 0 ≤ r) (hrk : r < 2*h+1)
    (hs : 1 ≤ s) (hsh : s ≤ h) :
    U h 1 Q (-s) + normU h 1 Q (r+s) ≤ 3 := by
  have h1 := odd_neg_le_two h s Q hh hs hsh hQ
  have hz : 0 ≤ r+s := by omega
  have hzk : r+s < 4*h+2 := by omega
  have h2 := odd_norm_pos_le_one h (r+s) Q hh hz hzk hQ
  calc U h 1 Q (-s) + normU h 1 Q (r+s) ≤ 2+1 := Int.add_le_add h1 h2
       _ ≤ 3 := by omega

-- The only corner where the separate upper bounds 3 and 2 are insufficient.
-- Here the strict n>n_k condition is exactly the lower bound r>=2.

theorem odd_corner_negative (h r u : Int) (hh : 1 ≤ h)
    (hr : 2 ≤ r) (_hrk : r < 2*h+1) (hu : 1 ≤ u) (huh : u ≤ h)
    (hB : r+u < 2*h+1) :
    U h 1 (h+1) (r+u) + U h 1 (h+2) (-u) ≤ 3 := by
  have hz : 0 ≤ r+u := by omega
  have hnu : -u ≤ -1 := by omega
  have hnl : -h ≤ -u := by omega
  rw [odd_pos_low h (r+u) (h+1) hh hz hB rfl,
      odd_neg_low h (-u) (h+2) hh hnu hnl rfl]
  omega


theorem odd_corner_positive (h r B : Int) (hh : 1 ≤ h)
    (hr : 2 ≤ r) (hrk : r < 2*h+1) (hB : 1 ≤ B)
    (hBk : B < 2*h+1) (hz : 0 ≤ r-B) :
    U h 1 (h+1) B + U h 1 (h+2) (r-B) ≤ 3 := by
  have hB0 : 0 ≤ B := by omega
  have hzk : r-B < 2*h+1 := by omega
  rw [odd_pos_low h B (h+1) hh hB0 hBk rfl,
      odd_pos_middle h (r-B) (h+2) hh hz hzk rfl]
  omega


theorem primary_le_two (h kp C : Int) (hkp : kp=0 ∨ kp=1)
    (hh : 2 ≤ h) (hC : 2 ≤ C) : U h kp C 0 ≤ 2 := by
  rcases hkp with h0 | h1
  · subst kp
    by_cases hc : C=2
    · rw [primary_0_2 h 0 C hh rfl hc]
    · by_cases hc' : C=3
      · rw [primary_0_3 h 0 C hh rfl hc']
        omega
      · have hc4 : 4 ≤ C := by omega
        rw [primary_0_high h 0 C hh rfl hc4]
        omega
  · subst kp
    have hh2 : 1 ≤ h := by omega
    by_cases hc : C=2
    · rw [primary_1_2 h 0 C hh2 rfl hc]
    · by_cases hc' : C=3
      · rw [primary_1_3 h 0 C hh2 rfl hc']
        omega
      · have hc4 : 4 ≤ C := by omega
        rw [primary_1_high h 0 C hh2 rfl hc4]
        omega


end PetersenTables
```

### `PetersenFullU.lean`

```lean
import PetersenUTableDefs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PetersenTables
open scoped BigOperators

/-- The complete finite U sum from the written proof, before six-term truncation. -/
def fullU (h kp C z : ℤ) : ℤ :=
  ∑ t ∈ Finset.Icc 1 (h+1), (term h kp C z t (-1)+term h kp C z t 1)

private theorem sum_last_three (h : ℤ) (hh : 1 ≤ h) (g : ℤ → ℤ)
    (hsmall : ∀ t, 1 ≤ t → t ≤ h-2 → g t = 0)
    (hzero : h = 1 → g 0 = 0) :
    (∑ t ∈ Finset.Icc 1 (h+1), g t) = g (h-1)+g h+g (h+1) := by
  classical
  by_cases he : h = 1
  · subst h
    have hset : Finset.Icc (1 : ℤ) 2 = {1,2} := by decide
    rw [show (1 : ℤ)+1 = 2 by decide, hset]
    simp [hzero rfl]
  · have hh2 : 2 ≤ h := by omega
    have hsub : ({h-1,h,h+1} : Finset ℤ) ⊆ Finset.Icc 1 (h+1) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
    have hs := Finset.sum_subset (f := g) hsub (by
      intro t ht hnot
      have ht' := Finset.mem_Icc.mp ht
      have hn : t ≠ h-1 ∧ t ≠ h ∧ t ≠ h+1 := by simpa using hnot
      exact hsmall t ht'.1 (by omega))
    rw [← hs]
    simp [show h-1 ≠ h by omega, show h-1 ≠ h+1 by omega, show h ≠ h+1 by omega, add_assoc]

theorem term_small (h kp C z t e : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hz : -h ≤ z) (hzk : z < 2*h+kp) (hC : h+1 ≤ C)
    (ht : 0 ≤ t) (hth : t ≤ h-2) (he : e = -1 ∨ e = 1) :
    term h kp C z t e = 0 := by
  rcases he with rfl | rfl <;> simp only [term, pulse, sgn, localG, neg_one_mul, one_mul]
    <;> omega

theorem term_zero (h kp C z e : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hz : -h ≤ z) (hzk : z < 2*h+kp) (hC : h+1 ≤ C) :
    term h kp C z 0 e = 0 := by
  simp only [term, mul_zero, add_zero, pulse, sgn, localG]
  omega

/-- The table's six terms equal the *entire* U sum for all relevant positive/negative ranges. -/
theorem fullU_eq_U (h kp C z : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hz : -h ≤ z) (hzk : z < 2*h+kp) (hC : h+1 ≤ C) :
    fullU h kp C z = U h kp C z := by
  unfold fullU
  rw [sum_last_three h hh]
  · unfold U; omega
  · intro t ht hth
    rw [term_small h kp C z t (-1) hh hkp hz hzk hC (by omega) hth (Or.inl rfl),
      term_small h kp C z t 1 hh hkp hz hzk hC (by omega) hth (Or.inr rfl)]
    omega
  · intro _
    rw [term_zero h kp C z (-1) hh hkp hz hzk hC,
      term_zero h kp C z 1 hh hkp hz hzk hC]
    omega

end PetersenTables
```

### `PetersenSignedLine.lean`

```lean
import PetersenUTableDefs

namespace Petersen
/-- The signed sawtooth extension; used internally in the counting proof. -/
def g (k x : ℤ) : ℤ := x/k + min (x%k) (k+1-x%k)

theorem g_block (k a b : ℤ) (hk : 0 < k) (hb : 0 ≤ b) (hbk : b < k) :
    g k (a*k+b) = a+min b (k+1-b) := by
  simp [g, Int.mul_add_ediv_right _ _ (ne_of_gt hk), Int.add_emod,
    Int.emod_eq_of_lt hb hbk, Int.ediv_eq_zero_of_lt hb hbk]

theorem g_nat (k x : ℕ) (hk : 0 < k) : g k x = (lineCost k x : ℤ) := by
  rw [lineCost_cast hk]
  simp only [g, Int.natCast_ediv, Int.natCast_emod]

/-- This is the missing semantic bridge from the table's finite piecewise function. -/
theorem localG_eq_g (k x : ℤ) (hk : 3 ≤ k) (hlo : -k-1 ≤ x) (hhi : x ≤ 2*k) :
    PetersenTables.localG k x = g k x := by
  by_cases h1 : x < -k
  · have hx : x = -2*k+(k-1) := by omega
    rw [hx, g_block k (-2) (k-1) (by omega) (by omega) (by omega)]
    unfold PetersenTables.localG
    omega
  · by_cases h2 : x < 0
    · have hx : x = -1*k+(k+x) := by ring
      rw [hx, g_block k (-1) (k+x) (by omega) (by omega) (by omega)]
      unfold PetersenTables.localG
      omega
    · by_cases h3 : x < k
      · have hx : x = 0*k+x := by ring
        conv_rhs => rw [hx, g_block k 0 x (by omega) (by omega) h3]
        unfold PetersenTables.localG
        omega
      · by_cases h4 : x < 2*k
        · have hx : x = 1*k+(x-k) := by ring
          conv_rhs => rw [hx, g_block k 1 (x-k) (by omega) (by omega) (by omega)]
          unfold PetersenTables.localG
          omega
        · have hx : x = 2*k+0 := by omega
          rw [hx, g_block k 2 0 (by omega) (by omega) (by omega)]
          unfold PetersenTables.localG
          omega

end Petersen

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem g_translate (k a x : ℤ) (hk : 0 < k) : g k (a*k+x) = a+g k x := by
  simp [g, Int.mul_add_ediv_right _ _ (ne_of_gt hk), Int.add_emod, add_assoc]

theorem f_int_lift (hk : 0 < k) (x : ℤ) (hx : 0 ≤ x) (hxn : x < n) :
    (f n k (x : ZMod n) : ℤ) = min (g k x) (g k ((n : ℤ)-x)) := by
  have hnat : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx
  have hlt : x.toNat < n := by omega
  have hcast : ((x.toNat : ℕ) : ZMod n) = (x : ZMod n) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod n)) hnat
  rw [← hcast]
  unfold f
  rw [ZMod.val_natCast_of_lt hlt, Nat.cast_min, ← g_nat k _ hk, ← g_nat k _ hk]
  rw [Nat.cast_sub (by omega : x.toNat ≤ n), hnat]

end Petersen
```

### `PetersenUBridge.lean`

```lean
import PetersenFullU
import PetersenSignedLine

namespace PetersenTables
open scoped BigOperators

private theorem primary_small (h kp C t e : ℤ) (_hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hC : 2 ≤ C) (ht : 0 ≤ t) (hth : t ≤ h-2) (he : e = -1 ∨ e = 1) :
    term h kp C 0 t e = 0 := by
  rcases he with rfl | rfl <;> simp only [term, pulse, sgn, localG, zero_add, neg_one_mul, one_mul]
    <;> omega

/-- The low-primary columns need C≥2, rather than C≥h+1. -/
theorem fullU_primary_eq_U (h kp C : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hC : 2 ≤ C) : fullU h kp C 0 = U h kp C 0 := by
  classical
  by_cases he : h = 1
  · subst h
    have hset : Finset.Icc (1 : ℤ) 2 = {1,2} := by decide
    simp only [fullU, show (1 : ℤ)+1 = 2 by decide, hset]
    have hz (e : ℤ) : term 1 kp C 0 0 e = 0 := by
      simp only [term, mul_zero, add_zero, pulse, sgn, localG]; omega
    simp [U, hz]
    ring
  · have hh2 : 2 ≤ h := by omega
    let s : Finset ℤ := {h-1,h,h+1}
    have hsub : s ⊆ Finset.Icc 1 (h+1) := by
      intro t ht
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
    have hs := Finset.sum_subset (f := fun t => term h kp C 0 t (-1)+term h kp C 0 t 1) hsub (by
      intro t ht hnot
      have ht' := Finset.mem_Icc.mp ht
      have hn : t ≠ h-1 ∧ t ≠ h ∧ t ≠ h+1 := by simpa [s] using hnot
      rw [primary_small h kp C t (-1) hh hkp hC (by omega) (by omega) (Or.inl rfl),
        primary_small h kp C t 1 hh hkp hC (by omega) (by omega) (Or.inr rfl)]
      omega)
    unfold fullU
    rw [← hs]
    simp [s, U, show h-1 ≠ h by omega, show h-1 ≠ h+1 by omega, show h ≠ h+1 by omega]
    ring

/-- The untruncated sum with the actual signed line metric. -/
def signedU (h kp C z : ℤ) : ℤ :=
  ∑ t ∈ Finset.Icc 1 (h+1),
    (Petersen.pulse t (min t (2*h+kp+1-t)+2) (1+C+Petersen.g (2*h+kp) (z-t)) +
     Petersen.pulse t (min t (2*h+kp+1-t)+2) (1+C+Petersen.g (2*h+kp) (z+t)))

theorem fullU_eq_signedU (h kp C z : ℤ) (_hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hk : 3 ≤ 2*h+kp) (hz : -h ≤ z) (hzk : z < 2*h+kp) :
    fullU h kp C z = signedU h kp C z := by
  unfold fullU signedU
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_Icc.mp ht
  simp only [term, neg_one_mul, one_mul, pulse_eq, ← sub_eq_add_neg]
  rw [Petersen.localG_eq_g (2*h+kp) (z-t) hk (by omega) (by omega),
    Petersen.localG_eq_g (2*h+kp) (z+t) hk (by omega) (by omega)]

end PetersenTables
```

### `PetersenStageTwoAudit.lean`

```lean
import PetersenAudit
import PetersenSymmetry
import PetersenBalanceCounts
import PetersenOuterSupport
import PetersenPulses
import PetersenOuterSum
import PetersenInnerArithmetic
import PetersenSelectedRoots
import PetersenInnerWitness
import PetersenLowInner
import PetersenUTableDefs
import PetersenUTablesPositive
import PetersenUTablesNegative
import PetersenUTablesPrimary
import PetersenUTableBounds
import PetersenFullU
import PetersenSignedLine
import PetersenUBridge

#check Petersen.same_layer_balanced
#check Petersen.closerCount_eq
#check Petersen.cancellation
#check Petersen.outer_shortcut_iff
#check Petersen.outer_shortcut_values
#check Petersen.outerCount_strip
#check Petersen.innerPulse_route
#check Petersen.innerCount_selected
#check Petersen.innerCount_four_roots
#check Petersen.rootIndex_injective
#check Petersen.f_inner_multiple
#check Petersen.f_cross_blocks
#check Petersen.innerCount_four_blocks
#check Petersen.low_inner
#check Petersen.g_nat
#check Petersen.localG_eq_g
#check Petersen.f_int_lift
#check Petersen.strict_imbalance_of_counts
#print axioms Petersen.same_layer_balanced
#print axioms Petersen.closerCount_eq
#print axioms Petersen.cancellation
#print axioms Petersen.outer_shortcut_iff
#print axioms Petersen.outer_shortcut_values
#print axioms Petersen.outerCount_strip
#print axioms Petersen.innerPulse_route
#print axioms Petersen.innerCount_selected
#print axioms Petersen.innerCount_four_roots
#print axioms Petersen.rootIndex_injective
#print axioms Petersen.f_inner_multiple
#print axioms Petersen.f_cross_blocks
#print axioms Petersen.innerCount_four_blocks
#print axioms Petersen.low_inner
#print axioms Petersen.g_nat
#print axioms Petersen.localG_eq_g
#print axioms Petersen.f_int_lift
#print axioms Petersen.strict_imbalance_of_counts
#print axioms PetersenTables.fullU_eq_U
#print axioms PetersenTables.fullU_primary_eq_U
#print axioms PetersenTables.fullU_eq_signedU
#print axioms PetersenTables.even_pos_low
#print axioms PetersenTables.even_pos_high
#print axioms PetersenTables.odd_pos_low
#print axioms PetersenTables.odd_pos_middle
#print axioms PetersenTables.odd_pos_high
#print axioms PetersenTables.even_neg_low
#print axioms PetersenTables.even_neg_middle
#print axioms PetersenTables.even_neg_high
#print axioms PetersenTables.odd_neg_low
#print axioms PetersenTables.odd_neg_middle
#print axioms PetersenTables.odd_neg_high
#print axioms PetersenTables.primary_le_two
#print axioms PetersenTables.odd_corner_negative
#print axioms PetersenTables.odd_corner_positive
```

### `PetersenOuterBridge.lean`

```lean
import PetersenOuterSum
import PetersenUBridge
import Mathlib.Algebra.BigOperators.Intervals

set_option linter.unusedSimpArgs false

namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- Pair the positive and negative positions once, for every outer sum. -/
theorem sum_symmetric (m : ℕ) (v : ℤ → ℤ) :
    (∑ z ∈ Finset.Icc (-(m : ℤ)) m, v z) =
      v 0 + ∑ t ∈ Finset.Icc 1 (m : ℤ), (v (-t)+v t) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    have hset : Finset.Icc (-((m+1 : ℕ) : ℤ)) (m+1 : ℕ) =
        insert (-((m+1 : ℕ) : ℤ)) (insert ((m+1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) m)) := by
      ext z
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hsetp : Finset.Icc (1 : ℤ) (m+1 : ℕ) =
        insert ((m+1 : ℕ) : ℤ) (Finset.Icc 1 (m : ℤ)) := by
      ext z
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, hsetp]
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega)]
    rw [ih]
    ring

/-- The two line lifts majorize the actual outer count. Quotients and offsets
are unrestricted; only the seam separation and the vanishing origin are used. -/
theorem outerCount_le_signedU (hk : 3 ≤ k) (hn : k*(k+2) ≤ n)
    (A B Ap Bp : ℤ) (hj : (k/2+1 : ℕ) ≤ A*(k : ℤ)+B)
    (hjn : A*(k : ℤ)+B+(k/2+1 : ℕ) < n)
    (hs : (n : ℤ) = (A*k+B)+(Ap*k+Bp))
    (hf : 2 ≤ f n k ((A*(k : ℤ)+B : ℤ) : ZMod n)) :
    outerCount n k ((A*(k : ℤ)+B : ℤ) : ZMod n) ≤
      PetersenTables.signedU (k/2 : ℕ) (k%2 : ℕ) A B +
      PetersenTables.signedU (k/2 : ℕ) (k%2 : ℕ) Ap Bp := by
  have hk0 : 0 < k := by omega
  have hpar : (2 : ℤ)*(k/2 : ℕ)+(k%2 : ℕ) = k := by omega
  have hH (t : ℕ) (ht : t ≤ k/2+1) :
      (H k t : ℤ) = min (t : ℤ) ((k : ℤ)+1-t) := by
    unfold H
    rw [Nat.cast_min, Nat.cast_sub (by omega : t ≤ k+1)]
    push_cast
    rfl
  have hp (t : ℤ) (ht : 1 ≤ t) (htm : t ≤ (k/2+1 : ℕ)) :
      (t.natAbs : ℤ) = t ∧ (H k t.natAbs : ℤ) = min t ((k : ℤ)+1-t) := by
    have hab : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    refine ⟨hab, ?_⟩
    rw [hH t.natAbs (by omega), hab]
  rw [outerCount_strip hk hn, sum_symmetric]
  have horigin : pulse (0 : ℤ) (H k 0+2) (f n k ((0 : ZMod n)-↑(A*↑k+B))+1) = 0 := by
    rw [zero_sub, f_neg (by omega) hn]
    simp only [H, pulse, sign]
    split_ifs <;> omega
  simp only [Int.natAbs_zero, Nat.cast_zero, Int.cast_zero, horigin, zero_add]
  unfold PetersenTables.signedU
  rw [hpar]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have ht' := Finset.mem_Icc.mp ht
  have htlo : 1 ≤ t := ht'.1
  have hthi : t ≤ (k/2+1 : ℕ) := by exact_mod_cast ht'.2
  have hb := hp t htlo hthi
  have hbn : ((-t).natAbs : ℤ) = t := by simpa only [Int.natAbs_neg] using hb.1
  have hHn : (H k (-t).natAbs : ℤ) = min t ((k : ℤ)+1-t) := by simpa using hb.2
  have hbranch (z : ℤ) (hz : |z| ≤ (k/2+1 : ℕ)) :
      (f n k ((z : ZMod n)-(↑(A*↑k+B))) : ℤ) =
        min (A+g k (B-z)) (Ap+g k (Bp+z)) := by
    have he : (z : ZMod n)-↑(A*↑k+B) = -(((A*↑k+B-z : ℤ) : ZMod n)) := by push_cast; ring
    rw [he, f_neg (by omega) hn, f_int_lift hk0 _ (by have := abs_le.mp hz; omega)
      (by have := abs_le.mp hz; omega)]
    have hx : (n : ℤ)-(A*↑k+B-z) = Ap*↑k+(Bp+z) := by linarith
    rw [hx, show A*↑k+B-z = A*↑k+(B-z) by ring, g_translate _ _ _ (by omega),
      g_translate _ _ _ (by omega)]
  have hpulse (z : ℤ) (hz : |z| ≤ (k/2+1 : ℕ)) :
      pulse z.natAbs (H k z.natAbs+2) (f n k ((z : ZMod n)-↑(A*↑k+B))+1) ≤
        pulse z.natAbs (H k z.natAbs+2) (1+A+g k (B-z)) +
        pulse z.natAbs (H k z.natAbs+2) (1+Ap+g k (Bp+z)) := by
    have ha : (z.natAbs : ℤ) ≤ H k z.natAbs+2 := by
      rw [hH z.natAbs (by exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hz))]
      have hab : |z| ≤ (k/2+1 : ℕ) := hz
      rw [Int.natCast_natAbs]
      omega
    rw [hbranch z hz]
    have he : min (A+g k (B-z)) (Ap+g k (Bp+z))+1 =
        min (1+A+g k (B-z)) (1+Ap+g k (Bp+z)) := by omega
    rw [he]
    exact pulse_min_bound _ _ _ _ ha
  have hpos := hpulse t (by rw [abs_of_nonneg (by omega)]; exact hthi)
  have hneg := hpulse (-t) (by rw [abs_neg, abs_of_nonneg (by omega)]; exact hthi)
  simp only [hb.1, hb.2, hbn, hHn, Nat.cast_add, Nat.cast_ofNat, sub_neg_eq_add, ← sub_eq_add_neg] at hpos hneg ⊢
  linarith

end Petersen
```

### `PetersenInnerLifts.lean`

```lean
import PetersenInnerWitness
import PetersenSignedLine

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- A signed-lift form of the four-root bound. It avoids canonical-remainder
case splits: the two root-depth inequalities subsume both axis conditions. -/
theorem innerCount_four_lifts (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (x C Cp : ℤ) (hx : 0 < x) (hxn : x < n)
    (hc : g k x = C) (hcp : g k ((n : ℤ)-x) = Cp)
    (hC : 2 ≤ C) (hCp : 2 ≤ Cp)
    (hT : C ≤ 2*((n/k+H k (n%k))/2 : ℕ))
    (hTp : Cp ≤ 2*((n/k+H k (n%k))/2 : ℕ))
    (hdepth : (k : ℤ)*((C+1)/2) ≤ x)
    (hdepthp : (k : ℤ)*((Cp+1)/2) ≤ (n : ℤ)-x)
    (hwidth : (k : ℤ)*((C+1)/2+(Cp+1)/2) < n) :
    4 ≤ innerCount n k (x : ZMod n) := by
  have hk0 : 0 < k := by omega
  have hq : k+2 ≤ n/k := (Nat.le_div_iff_mul_le hk0).mpr (by nlinarith)
  have hH : H k (n%k) ≤ k+1 := by unfold H; omega
  have hfull (c : ℤ) (hc2 : 2 ≤ c) (hct : c ≤ 2*((n/k+H k (n%k))/2 : ℕ))
      (t : ℤ) (ht : t ∈ roots c) :
      f n k ((k : ZMod n)*(t : ZMod n)) = t.natAbs := by
    have hb := root_bounds c t hc2 ht
    have hnat : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have htq : t.natAbs ≤ n/k := by omega
    have htT : 2*t.natAbs ≤ n/k+H k (n%k) := by omega
    have he : ((t.natAbs : ℕ) : ZMod n) = (t : ZMod n) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod n)) hnat
    simpa only [Nat.cast_mul, he] using f_inner_full hk hn t.natAbs htq htT
  have hcross (y c cp : ℤ) (hy : 0 < y) (hyn : y < n)
      (hcy : g k y = c) (hcp' : g k ((n : ℤ)-y) = cp)
      (hc2 : 2 ≤ c) (hdep : (k : ℤ)*((c+1)/2) ≤ y)
      (t : ℤ) (ht : t ∈ roots c) :
      (f n k ((y : ZMod n)-(k : ZMod n)*(t : ZMod n)) : ℤ) = min (c-t) (cp+t) := by
    have hb := root_bounds c t hc2 ht
    have hkt : (k : ℤ)*t ≤ y := (mul_le_mul_of_nonneg_left hb.2.1 (by omega)).trans hdep
    have he : (y : ZMod n)-(k : ZMod n)*(t : ZMod n) = ((y-k*t : ℤ) : ZMod n) := by push_cast; rfl
    rw [he, f_int_lift hk0 _ (by omega) (by nlinarith)]
    have h1 : g k (y-k*t) = c-t := by
      rw [show y-(k : ℤ)*t = (-t)*k+y by ring, g_translate _ _ _ (by omega), hcy]
      ring
    have h2 : g k ((n : ℤ)-(y-k*t)) = cp+t := by
      rw [show (n : ℤ)-(y-k*t) = t*k+((n : ℤ)-y) by ring,
        g_translate _ _ _ (by omega), hcp']
      ring
    rw [h1, h2]
  apply innerCount_four_roots hk hn _ C Cp hC hCp (rootIndex_injective hk _ _ hC hCp hwidth)
  · exact hfull C hC hT
  · intro t ht
    have he : (k : ZMod n)*((-t : ℤ) : ZMod n) = -((k : ZMod n)*(t : ZMod n)) := by push_cast; ring
    rw [he, f_neg hk hn, Int.natAbs_neg]
    exact hfull Cp hCp hTp t ht
  · exact hcross x C Cp hx hxn hc hcp hC hdepth
  · intro t ht
    have he : (x : ZMod n)-(k : ZMod n)*((-t : ℤ) : ZMod n) =
        -((((n : ℤ)-x : ℤ) : ZMod n)-(k : ZMod n)*(t : ZMod n)) := by
      push_cast
      simp only [ZMod.natCast_self, zero_sub]
      ring
    rw [he, f_neg hk hn]
    apply hcross ((n : ℤ)-x) Cp C (by omega) (by omega) hcp _ hCp hdepthp t ht
    simpa only [sub_sub_cancel] using hc

end Petersen
```

### `PetersenUApplication.lean`

```lean
import PetersenOuterBridge
import PetersenUTableBounds

namespace PetersenTables
open scoped BigOperators

theorem signedU_translate (h kp C z : ℤ) (hk : 0 < 2*h+kp) :
    signedU h kp C (2*h+kp+z) = signedU h kp (C+1) z := by
  unfold signedU
  apply Finset.sum_congr rfl
  intro t _
  have he1 : 2*h+kp+z-t = 1*(2*h+kp)+(z-t) := by ring
  have he2 : 2*h+kp+z+t = 1*(2*h+kp)+(z+t) := by ring
  rw [he1, he2, Petersen.g_translate _ _ _ hk, Petersen.g_translate _ _ _ hk]
  congr 2 <;> ring

theorem signedU_eq_U (h kp C z : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hk : 3 ≤ 2*h+kp) (hz : -h ≤ z) (hzk : z < 2*h+kp) (hC : h+1 ≤ C) :
    signedU h kp C z = U h kp C z := by
  rw [← fullU_eq_signedU h kp C z hh hkp hk hz hzk, fullU_eq_U h kp C z hh hkp hz hzk hC]

theorem signedU_primary (h kp C : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hk : 3 ≤ 2*h+kp) (hC : 2 ≤ C) : signedU h kp C 0 = U h kp C 0 := by
  rw [← fullU_eq_signedU h kp C 0 hh hkp hk (by omega) (by omega),
    fullU_primary_eq_U h kp C hh hkp hC]

theorem signedU_eq_normU (h kp C z : ℤ) (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1)
    (hk : 3 ≤ 2*h+kp) (hz : -h ≤ z) (hzk : z < 2*(2*h+kp)) (hC : h+1 ≤ C) :
    signedU h kp C z = normU h kp C z := by
  unfold normU
  split
  · exact signedU_eq_U h kp C z hh hkp hk (by omega) (by omega) hC
  · have he : z = 2*h+kp+(z-(2*h+kp)) := by ring
    conv_lhs => rw [he]
    rw [signedU_translate h kp C _ (by omega)]
    exact signedU_eq_U h kp (C+1) (z-(2*h+kp)) hh hkp hk (by omega) (by omega) (by omega)

/-- Includes the h=1 odd case absent from the older combined bound. -/
theorem primary_le_two_all (h kp C : ℤ) (hkp : kp = 0 ∨ kp = 1)
    (hh : 1 ≤ h) (hk : 3 ≤ 2*h+kp) (hC : 2 ≤ C) : U h kp C 0 ≤ 2 := by
  by_cases he : 2 ≤ h
  · exact primary_le_two h kp C hkp he hC
  · have hh1 : h = 1 := by omega
    have hkp1 : kp = 1 := by rcases hkp with h0 | h1 <;> omega
    subst h; subst kp
    by_cases h2 : C = 2
    · rw [primary_1_2 1 0 C (by omega) rfl h2]
    · by_cases h3 : C = 3
      · rw [primary_1_3 1 0 C (by omega) rfl h3]; omega
      · rw [primary_1_high 1 0 C (by omega) rfl (by omega)]; omega

end PetersenTables
```

### `PetersenLowWitness.lean`

```lean
import PetersenUApplication
import PetersenLowInner

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem low_outer (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (a : ℕ)
    (ha : 2 ≤ a) (haq : a ≤ (n/k)/2) :
    outerCount n k (((a*k : ℕ) : ZMod n)) ≤ 3 := by
  have hk0 : 0 < k := by omega
  have hq : k+2 ≤ n/k := (Nat.le_div_iff_mul_le hk0).mpr (by nlinarith)
  have hr := Nat.mod_lt n hk0
  have hd := Nat.div_add_mod n k
  have haqn : a ≤ n/k := by omega
  have hi : ((n : ℕ) : ℤ) = (a : ℤ)*k+0+((n/k-a : ℕ) : ℤ)*k+(n%k : ℕ) := by
    have hd' : (n : ℤ) = (n/k : ℕ)*(k : ℤ)+(n%k : ℕ) := by exact_mod_cast (by simpa only [mul_comm] using hd.symm : n = n/k*k+n%k)
    rw [Nat.cast_sub haqn]
    nlinarith only [hd']
  have hc : ((a*(k : ℤ)+0 : ℤ) : ZMod n) = ((a*k : ℕ) : ZMod n) := by push_cast; ring
  have hf := (low_inner hk hn a ha haq).1
  have hm : (k/2+1 : ℕ) ≤ (a : ℤ)*k+0 := by
    have hm : (k/2+1 : ℕ) ≤ k := by omega
    have hm' : (k/2+1 : ℕ) ≤ (k : ℤ) := by exact_mod_cast hm
    nlinarith
  have hmn : (a : ℤ)*k+0+(k/2+1 : ℕ) < n := by
    have hqa : a+1 ≤ n/k := by omega
    have hqai : (a : ℤ)+1 ≤ (n/k : ℕ) := by exact_mod_cast hqa
    have hki : (0 : ℤ) < k := by omega
    have hm' : (k/2+1 : ℕ) < (k : ℤ) := by omega
    have hqkn : ((n/k : ℕ) : ℤ)*k ≤ n := by exact_mod_cast Nat.div_mul_le_self n k
    nlinarith
  have hb := outerCount_le_signedU hk hn a 0 (n/k-a : ℕ) (n%k : ℕ) hm hmn
    (by linarith only [hi]) (by rw [hc, hf]; exact ha)
  rw [hc] at hb
  have hpar : (2 : ℤ)*(k/2 : ℕ)+(k%2 : ℕ) = k := by omega
  have hkp : ((k%2 : ℕ) : ℤ) = 0 ∨ ((k%2 : ℕ) : ℤ) = 1 := by omega
  have hh : (1 : ℤ) ≤ (k/2 : ℕ) := by omega
  rw [PetersenTables.signedU_primary _ _ _ hh hkp (by omega) (by omega),
    PetersenTables.signedU_eq_U _ _ _ _ hh hkp (by omega) (by omega) (by omega) (by omega)] at hb
  have h1 := PetersenTables.primary_le_two_all (k/2 : ℕ) (k%2 : ℕ) a hkp hh (by omega) (by omega)
  have h2 : PetersenTables.U (k/2 : ℕ) (k%2 : ℕ) (n/k-a : ℕ) (n%k : ℕ) ≤ 1 := by
    rcases hkp with he | he
    · rw [he]
      apply PetersenTables.even_pos_le_one <;> omega
    · rw [he]
      apply PetersenTables.odd_pos_le_one <;> omega
  omega

/-- Unconditional strict imbalance on the whole low middle-radius range. -/
theorem witness_low (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (a : ℕ)
    (ha : 2 ≤ a) (haq : a ≤ (n/k)/2) :
    f n k (((a*k : ℕ) : ZMod n)) = a ∧
      outerCount n k (((a*k : ℕ) : ZMod n)) ≤ 3 ∧
      4 ≤ innerCount n k (((a*k : ℕ) : ZMod n)) :=
  ⟨(low_inner hk hn a ha haq).1, low_outer hk hn a ha haq, (low_inner hk hn a ha haq).2⟩

theorem low_strict_imbalance (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (a : ℕ)
    (ha : 2 ≤ a) (haq : a ≤ (n/k)/2) :
    imbalance n k (((a*k : ℕ) : ZMod n)) < 0 := by
  have h := witness_low hk hn a ha haq
  rw [cancellation (by omega) hn]
  omega

theorem low_not_LDB (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) (ell : ℕ)
    (h3 : 3 ≤ ell) (hq : ell ≤ (n/k)/2+1) : ¬ LDB (GP n k) ell := by
  have h := witness_low hk hn (ell-1) (by omega) (by omega)
  have hh := strict_imbalance_of_counts (by omega : 2 ≤ k) hn _ (by omega :
    outerCount n k (((((ell-1)*k) : ℕ) : ZMod n)) < innerCount n k (((((ell-1)*k) : ℕ) : ZMod n)))
  simpa only [h.1, Nat.sub_add_cancel (by omega : 1 ≤ ell)] using hh

end Petersen
```

### `PetersenHighRadius.lean`

```lean
import PetersenInnerLifts

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- The two possible remainder regions bound every attained level, not just
levels in the last quotient block. -/
theorem attained_cost_bound (hk : 3 ≤ k) (a : ℕ) (hex : ∃ j : ZMod n, f n k j = a) :
    (2*(a : ℤ) ≤ (n/k : ℕ)+(n%k : ℕ)) ∨
    (2*(a : ℤ) ≤ (n/k : ℕ)+(k : ℤ)-(n%k : ℕ)+1 ∧
      2*(a : ℤ) ≤ (n/k : ℕ)-1+2*((k+1)/2 : ℕ) ∧
      (n%k = 0 → 2*(a : ℤ) ≤ (n/k : ℕ)+(k : ℤ)-1)) := by
  obtain ⟨j, hj⟩ := hex
  have hk0 : 0 < k := by omega
  have hr := Nat.mod_lt n hk0
  have hb := Nat.mod_lt j.val hk0
  have hval := j.val_lt
  have hd := Nat.div_add_mod n k
  have hdj := Nat.div_add_mod j.val k
  have hcost : (a : ℤ) = min (g k j.val) (g k ((n : ℤ)-j.val)) := by
    rw [← hj]
    have he : ((j.val : ℕ) : ZMod n) = j := ZMod.natCast_zmod_val j
    simpa only [Int.cast_natCast, he] using f_int_lift (n := n) hk0 (j.val : ℤ) (by omega) (by omega)
  have hx : (j.val : ℤ) = (j.val/k : ℕ)*(k : ℤ)+(j.val%k : ℕ) := by exact_mod_cast (by simpa only [mul_comm] using hdj.symm : j.val = j.val/k*k+j.val%k)
  have hn' : (n : ℤ) = (n/k : ℕ)*(k : ℤ)+(n%k : ℕ) := by exact_mod_cast (by simpa only [mul_comm] using hd.symm : n = n/k*k+n%k)
  conv at hcost => rhs; lhs; rw [hx, g_block _ _ _ (by omega) (by omega) (by omega)]
  by_cases hbr : j.val%k ≤ n%k
  · left
    have he : (n : ℤ)-j.val = ((n/k : ℕ)-(j.val/k : ℕ))*(k : ℤ)+((n%k : ℕ)-(j.val%k : ℕ)) := by
      linear_combination hn'-hx
    rw [he, g_block _ _ _ (by omega) (by omega) (by omega)] at hcost
    omega
  · right
    have he : (n : ℤ)-j.val = ((n/k : ℕ)-(j.val/k : ℕ)-1)*(k : ℤ)+
        ((k : ℤ)+(n%k : ℕ)-(j.val%k : ℕ)) := by linear_combination hn'-hx
    rw [he, g_block _ _ _ (by omega) (by omega) (by omega)] at hcost
    have hm1 : min ((j.val%k : ℕ) : ℤ) ((k : ℤ)+1-(j.val%k : ℕ)) ≤ ((k+1)/2 : ℕ) := by omega
    have hm2 : min ((k : ℤ)+(n%k : ℕ)-(j.val%k : ℕ))
        ((k : ℤ)+1-((k : ℤ)+(n%k : ℕ)-(j.val%k : ℕ))) ≤ ((k+1)/2 : ℕ) := by omega
    refine ⟨by omega, by omega, ?_⟩
    intro hr0
    omega

end Petersen
```

### `PetersenCentralWitness.lean`

```lean
import PetersenUApplication
import PetersenInnerLifts

namespace Petersen
variable {n k : ℕ} [NeZero n]

private theorem depth_from_offset (A B C : ℤ) (hk : (0 : ℤ) < k)
    (hB : -(k : ℤ) ≤ B) (_hC : 2 ≤ C)
    (hd : (C+1)/2 ≤ A+(if B < 0 then -1 else 0)) :
    (k : ℤ)*((C+1)/2) ≤ A*k+B := by
  by_cases hb : B < 0
  · simp only [hb, ite_true] at hd
    have hm := mul_le_mul_of_nonneg_left hd (le_of_lt hk)
    nlinarith
  · simp only [hb, ite_false] at hd
    have hm := mul_le_mul_of_nonneg_left hd (le_of_lt hk)
    nlinarith

/-- Shared graph/count proof for all high-radius offset classes. The remaining
premises are linear sawtooth arithmetic and the already certified U tables. -/
theorem central_witness (hk : 3 ≤ k) (hn : k*(k+2) ≤ n)
    (Q eps r B : ℤ) (a : ℕ)
    (hqn : (n/k : ℕ) = 2*Q+eps) (hrn : (n%k : ℕ) = r)
    (hB : -(k : ℤ) ≤ B) (hBp : -(k : ℤ) ≤ r-B)
    (hlevel : min (Q+g k B) (Q+eps+g k (r-B)) = a) (ha : 2 ≤ a)
    (hT : Q+g k B ≤ 2*((n/k+H k (n%k))/2 : ℕ))
    (hTp : Q+eps+g k (r-B) ≤ 2*((n/k+H k (n%k))/2 : ℕ))
    (hdep : (Q+g k B+1)/2 ≤ Q+(if B < 0 then -1 else 0))
    (hdepp : (Q+eps+g k (r-B)+1)/2 ≤ Q+eps+(if r-B < 0 then -1 else 0))
    (hwide : (Q+g k B+1)/2+(Q+eps+g k (r-B)+1)/2 < 2*Q+eps)
    (houter : PetersenTables.signedU (k/2 : ℕ) (k%2 : ℕ) Q B +
      PetersenTables.signedU (k/2 : ℕ) (k%2 : ℕ) (Q+eps) (r-B) ≤ 3) :
    ∃ j : ZMod n, f n k j = a ∧ outerCount n k j ≤ 3 ∧ 4 ≤ innerCount n k j := by
  have hk0 : (0 : ℤ) < k := by omega
  have hC : 2 ≤ Q+g k B := by omega
  have hCp : 2 ≤ Q+eps+g k (r-B) := by omega
  have hx := depth_from_offset Q B (Q+g k B) hk0 hB hC hdep
  have hyp := depth_from_offset (Q+eps) (r-B) (Q+eps+g k (r-B)) hk0 hBp hCp hdepp
  have hs : (n : ℤ) = (Q*k+B)+((Q+eps)*k+(r-B)) := by
    have hd : (n : ℤ) = (n/k : ℕ)*(k : ℤ)+(n%k : ℕ) := by
      exact_mod_cast (by simpa only [mul_comm] using (Nat.div_add_mod n k).symm : n = n/k*k+n%k)
    rw [hqn, hrn] at hd
    nlinarith only [hd]
  have hxk : (k : ℤ) ≤ Q*k+B := by
    have ht : 1 ≤ (Q+g k B+1)/2 := by omega
    have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hk0)
    linarith
  have hyk : (k : ℤ) ≤ (Q+eps)*k+(r-B) := by
    have ht : 1 ≤ (Q+eps+g k (r-B)+1)/2 := by omega
    have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hk0)
    linarith
  have hxn : Q*(k : ℤ)+B < n := by linarith
  have hx0 : 0 < Q*(k : ℤ)+B := by linarith
  have hgc : g k (Q*(k : ℤ)+B) = Q+g k B := g_translate _ _ _ hk0
  have hgcp : g k ((n : ℤ)-(Q*k+B)) = Q+eps+g k (r-B) := by
    rw [show (n : ℤ)-(Q*k+B) = (Q+eps)*k+(r-B) by linarith,
      g_translate _ _ _ hk0]
  have hf : f n k ((Q*(k : ℤ)+B : ℤ) : ZMod n) = a := by
    have h := f_int_lift (n := n) (by omega : 0 < k) _ (by omega) hxn
    rw [hgc, hgcp, hlevel] at h
    exact_mod_cast h
  refine ⟨((Q*(k : ℤ)+B : ℤ) : ZMod n), hf, ?_, ?_⟩
  · exact (outerCount_le_signedU hk hn Q B (Q+eps) (r-B) (by omega) (by omega) hs (by omega)).trans houter
  · apply innerCount_four_lifts (by omega : 2 ≤ k) hn (Q*k+B) (Q+g k B) (Q+eps+g k (r-B))
      hx0 hxn hgc hgcp hC hCp hT hTp hx (by linarith only [hyp, hs])
    have hm := mul_lt_mul_of_pos_left hwide hk0
    have hle : (k : ℤ)*(2*Q+eps) ≤ n := by
      have hr0 : 0 ≤ r := by rw [← hrn]; omega
      nlinarith only [hs, hr0]
    exact hm.trans_le hle

end Petersen
```

### `PetersenHighOffsets.lean`

```lean
import PetersenUApplication

namespace Petersen
/-- The five arithmetic offset regimes in formula (13). -/
def HighOffset (k r eps s B : ℤ) : Prop :=
  (eps = 0 ∧ B = s ∧ 2*s ≤ r) ∨
  (eps = 0 ∧ B = -s ∧ 2*s ≤ k-r+1 ∧ 2*s ≤ 2*((k+1)/2)-1) ∨
  (eps = 1 ∧ r = 0 ∧ B = s ∧ s ≤ k/2) ∨
  (eps = 1 ∧ 1 ≤ r ∧ B = r+s-1 ∧ 2*s ≤ k-r+2 ∧ s ≤ (k+1)/2) ∨
  (eps = 1 ∧ 1 ≤ r ∧ B = r+1-s ∧ 2*s ≤ r+1)

end Petersen

namespace PetersenTables
set_option linter.unusedSimpArgs false

/-- One bound covers all five canonical offset regimes, including the odd
near-threshold corners and offsets requiring one normalization. -/
theorem high_offset_outer (h kp Q eps r s B : ℤ)
    (hh : 1 ≤ h) (hkp : kp = 0 ∨ kp = 1) (hk : 3 ≤ 2*h+kp)
    (heps : eps = 0 ∨ eps = 1) (hr : 0 ≤ r) (hrk : r < 2*h+kp)
    (hq : 2*h+kp+2 ≤ 2*Q+eps)
    (hstrict : 2*Q+eps = 2*h+kp+2 → kp < r)
    (hs : 1 ≤ s) (hoff : Petersen.HighOffset (2*h+kp) r eps s B) :
    signedU h kp Q B + signedU h kp (Q+eps) (r-B) ≤ 3 := by
  have hQ : h+1 ≤ Q := by rcases heps with he | he <;> rcases hkp with hp | hp <;> omega
  have hB : -h ≤ B ∧ B < 2*(2*h+kp) := by
    rcases hoff with h | h | h | h | h <;> rcases hkp with hp | hp <;> omega
  have hBp : -h ≤ r-B ∧ r-B < 2*(2*h+kp) := by
    rcases hoff with h | h | h | h | h <;> rcases hkp with hp | hp <;> omega
  rw [signedU_eq_normU h kp Q B hh hkp hk hB.1 hB.2 hQ,
    signedU_eq_normU h kp (Q+eps) (r-B) hh hkp hk hBp.1 hBp.2 (by rcases heps with he | he <;> omega)]
  rcases hkp with rfl | rfl
  · have hh2 : 2 ≤ h := by omega
    have hp (z C : ℤ) (hz : 0 ≤ z) (hzk : z < 4*h) (hc : h+1 ≤ C) : normU h 0 C z ≤ 1 :=
      even_norm_pos_le_one h z C hh2 hz hzk hc
    rcases hoff with ho | ho | ho | ho | ho
    · obtain ⟨he, hbs, hsr⟩ := ho
      subst eps
      rw [hbs] at *
      have h1 := hp s Q (by omega) (by omega) hQ
      have h2 := hp (r-s) Q (by omega) (by omega) hQ
      simpa only [add_zero] using (show normU h 0 Q s + normU h 0 Q (r-s) ≤ 3 by omega)
    · obtain ⟨rfl, rfl, hsr, hsh⟩ := ho
      simpa [normU, show -s < 2*h by omega] using
        even_evenq_negative h Q r s hh2 hQ hr (by omega) hs (by omega)
    · obtain ⟨he, hr0, hbs, hsh⟩ := ho
      subst eps; subst r
      rw [hbs] at *
      have h1 := hp s Q (by omega) (by omega) hQ
      have h2 := even_neg_le_one h s (Q+1) hh2 hs (by omega) (by omega)
      simpa [normU, show -s < 2*h by omega, show s < 2*h by omega] using
        (show U h 0 Q s + U h 0 (Q+1) (-s) ≤ 3 by
          have : U h 0 Q s ≤ 1 := by simpa [normU, show s < 2*h by omega] using h1
          omega)
    · obtain ⟨rfl, hr1, rfl, hsr, hsh⟩ := ho
      have h1 := hp (r+s-1) Q (by omega) (by omega) hQ
      by_cases he : s = 1
      · have h2 := hp (r-(r+s-1)) (Q+1) (by omega) (by omega) (by omega)
        omega
      · have h2 := even_neg_le_one h (s-1) (Q+1) hh2 (by omega) (by omega) (by omega)
        have he : r-(r+s-1) = -(s-1) := by ring
        rw [he]
        have hn : normU h 0 (Q+1) (-(s-1)) = U h 0 (Q+1) (-(s-1)) := by simp [normU]; omega
        rw [hn]; omega
    · obtain ⟨rfl, hr1, rfl, hsr⟩ := ho
      have h1 := hp (r+1-s) Q (by omega) (by omega) hQ
      have h2 := hp (r-(r+1-s)) (Q+1) (by omega) (by omega) (by omega)
      omega
  · have hp (z C : ℤ) (hz : 0 ≤ z) (hzk : z < 4*h+2) (hc : h+2 ≤ C) : normU h 1 C z ≤ 1 :=
      odd_norm_pos_le_one h z C hh hz hzk hc
    rcases hoff with ho | ho | ho | ho | ho
    · obtain ⟨he, hbs, hsr⟩ := ho
      subst eps
      rw [hbs] at *
      have hQ2 : h+2 ≤ Q := by omega
      have h1 := hp s Q (by omega) (by omega) hQ2
      have h2 := hp (r-s) Q (by omega) (by omega) hQ2
      simpa only [add_zero] using (show normU h 1 Q s + normU h 1 Q (r-s) ≤ 3 by omega)
    · obtain ⟨rfl, rfl, hsr, hsh⟩ := ho
      simpa [normU, show -s < 2*h+1 by omega] using
        odd_evenq_negative h Q r s hh (by omega) hr hrk hs (by omega)
    · obtain ⟨he, hr0, hbs, hsh⟩ := ho
      subst eps; subst r
      rw [hbs] at *
      have hQ2 : h+2 ≤ Q := by by_contra hn; have := hstrict (by omega); omega
      have h1 := hp s Q (by omega) (by omega) hQ2
      have h2 := odd_neg_le_one h s (Q+1) hh hs (by omega) (by omega)
      have hn1 : normU h 1 Q s = U h 1 Q s := by simp [normU]; omega
      have hn2 : normU h 1 (Q+1) (-s) = U h 1 (Q+1) (-s) := by simp [normU]; omega
      simp only [zero_sub, hn1, hn2] at *
      omega
    · obtain ⟨rfl, hr1, rfl, hsr, hsh⟩ := ho
      have hBk : r+s-1 < 2*h+1 := by omega
      have hn1 : normU h 1 Q (r+s-1) = U h 1 Q (r+s-1) := by simp [normU, hBk]
      have hn2 : normU h 1 (Q+1) (r-(r+s-1)) = U h 1 (Q+1) (-(s-1)) := by
        simp only [normU, ite_eq_left (by omega : r-(r+s-1) < 2*h+1)]
        congr 1; ring
      rw [hn1, hn2]
      by_cases he : Q = h+1
      · have hr2 : 2 ≤ r := by have := hstrict (by omega); omega
        by_cases hs1 : s = 1
        · rw [odd_pos_low h (r+s-1) Q hh (by omega) hBk he,
            odd_pos_middle h (-(s-1)) (Q+1) hh (by omega) (by omega) (by omega)]
          omega
        · have hcorner := odd_corner_negative h r (s-1) hh hr2 hrk (by omega) (by omega) (by omega)
          simpa only [he, show r+s-1 = r+(s-1) by ring, show h+1+1 = h+2 by ring] using hcorner
      · have h1 := odd_pos_le_one h (r+s-1) Q hh (by omega) hBk (by omega)
        by_cases hs1 : s = 1
        · have h2 := odd_pos_le_one h (-(s-1)) (Q+1) hh (by omega) (by omega) (by omega)
          omega
        · have h2 := odd_neg_le_one h (s-1) (Q+1) hh (by omega) (by omega) (by omega)
          omega
    · obtain ⟨rfl, hr1, rfl, hsr⟩ := ho
      by_cases he : Q = h+1
      · have hr2 : 2 ≤ r := by have := hstrict (by omega); omega
        have hh' := odd_corner_positive h r (r+1-s) hh hr2 hrk (by omega) (by omega) (by omega)
        simpa [normU, he, show r+1-s < 2*h+1 by omega, show r-(r+1-s) < 2*h+1 by omega, show h+1+1 = h+2 by ring] using hh'
      · have h1 := hp (r+1-s) Q (by omega) (by omega) (by omega)
        have h2 := hp (r-(r+1-s)) (Q+1) (by omega) (by omega) (by omega)
        omega

end PetersenTables
```

### `PetersenHighData.lean`

```lean
import PetersenHighOffsets

namespace Petersen
set_option maxHeartbeats 800000

/-- Linear arithmetic shared by the five high-offset regimes. In particular,
the root depths and disjointness are checked here, rather than left as graph
hypotheses on the final witness. -/
theorem high_offset_data (k Q eps r s B : ℤ) (hk : 3 ≤ k)
    (heps : eps = 0 ∨ eps = 1) (hr : 0 ≤ r) (hrk : r < k)
    (hq : k+2 ≤ 2*Q+eps) (hstrict : 2*Q+eps = k+2 → k%2 < r)
    (hs : 1 ≤ s) (hoff : HighOffset k r eps s B) :
    min (Q+g k B) (Q+eps+g k (r-B)) = Q+s ∧
    Q+g k B ≤ 2*Q ∧ Q+eps+g k (r-B) ≤ 2*Q ∧
    (Q+g k B+1)/2 ≤ Q+(if B < 0 then -1 else 0) ∧
    (Q+eps+g k (r-B)+1)/2 ≤ Q+eps+(if r-B < 0 then -1 else 0) ∧
    (Q+g k B+1)/2+(Q+eps+g k (r-B)+1)/2 < 2*Q+eps := by
  have hB : -k-1 ≤ B ∧ B ≤ 2*k := by
    rcases hoff with h | h | h | h | h <;> omega
  have hBp : -k-1 ≤ r-B ∧ r-B ≤ 2*k := by
    rcases hoff with h | h | h | h | h <;> omega
  rw [← localG_eq_g k B hk hB.1 hB.2, ← localG_eq_g k (r-B) hk hBp.1 hBp.2]
  rcases hoff with ho | ho | ho | ho | ho
  · obtain ⟨rfl, rfl, hsr⟩ := ho
    simp only [PetersenTables.localG]
    omega
  · obtain ⟨rfl, rfl, hsr, hsh⟩ := ho
    simp only [PetersenTables.localG]
    omega
  · obtain ⟨rfl, rfl, rfl, hsh⟩ := ho
    simp only [PetersenTables.localG]
    omega
  · obtain ⟨rfl, hr1, rfl, hsr, hsh⟩ := ho
    simp only [PetersenTables.localG]
    omega
  · obtain ⟨rfl, hr1, rfl, hsr⟩ := ho
    simp only [PetersenTables.localG]
    omega

end Petersen
```

### `PetersenHighWitness.lean`

```lean
import PetersenCentralWitness
import PetersenHighData
import PetersenHighRadius

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem high_offset_exists (hk : 3 ≤ k) (a : ℕ)
    (hex : ∃ j : ZMod n, f n k j = a) (hhigh : (n/k)/2 < a) :
    ∃ B : ℤ, HighOffset k (n%k : ℕ) (n/k%2 : ℕ) ((a : ℤ)-(n/k/2 : ℕ)) B := by
  have hr := Nat.mod_lt n (by omega : 0 < k)
  have heps : n/k%2 = 0 ∨ n/k%2 = 1 := by omega
  have hb := attained_cost_bound hk a hex
  have hs : 1 ≤ (a : ℤ)-(n/k/2 : ℕ) := by omega
  rcases heps with he | he
  · by_cases hsr : 2*((a : ℤ)-(n/k/2 : ℕ)) ≤ (n%k : ℕ)
    · exact ⟨(a : ℤ)-(n/k/2 : ℕ), Or.inl ⟨by omega, rfl, hsr⟩⟩
    · refine ⟨-((a : ℤ)-(n/k/2 : ℕ)), Or.inr (Or.inl ⟨by omega, rfl, ?_, ?_⟩)⟩
      · rcases hb with hb | hb <;> omega
      · have hhalf : (((k+1)/2 : ℕ) : ℤ) = ((k : ℤ)+1)/2 := by omega
        rcases hb with hb | hb <;> omega
  · by_cases hr0 : n%k = 0
    · refine ⟨(a : ℤ)-(n/k/2 : ℕ), Or.inr (Or.inr (Or.inl ⟨by omega, by omega, rfl, ?_⟩))⟩
      rcases hb with hb | hb
      · omega
      · have := hb.2.2 hr0
        omega
    · by_cases hsmall : 2*((a : ℤ)-(n/k/2 : ℕ)) ≤ (k : ℤ)-(n%k : ℕ)+2 ∧
          (a : ℤ)-(n/k/2 : ℕ) ≤ ((k : ℤ)+1)/2
      · exact ⟨(n%k : ℕ)+((a : ℤ)-(n/k/2 : ℕ))-1,
          Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, rfl, hsmall.1, hsmall.2⟩)))⟩
      · refine ⟨(n%k : ℕ)+1-((a : ℤ)-(n/k/2 : ℕ)),
          Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, rfl, ?_⟩)))⟩
        have hhalf : (((k+1)/2 : ℕ) : ℤ) = ((k : ℤ)+1)/2 := by omega
        rcases hb with hb | hb <;> omega

/-- Every attained high radius has an unconditional strict-count witness. -/
theorem witness_high (hk : 3 ≤ k) (hn : nk k < n) (a : ℕ)
    (hhigh : (n/k)/2 < a) (hex : ∃ j : ZMod n, f n k j = a) :
    ∃ j : ZMod n, f n k j = a ∧ outerCount n k j ≤ 3 ∧ 4 ≤ innerCount n k j := by
  have hmetric := threshold_metric (by omega : 2 ≤ k) hn
  have hquot := (threshold_quotient hk).mp hn
  have hr := Nat.mod_lt n (by omega : 0 < k)
  have hqn : ((n/k : ℕ) : ℤ) = 2*(n/k/2 : ℕ)+(n/k%2 : ℕ) := by omega
  have hkp : ((k%2 : ℕ) : ℤ) = 0 ∨ ((k%2 : ℕ) : ℤ) = 1 := by omega
  have heps : ((n/k%2 : ℕ) : ℤ) = 0 ∨ ((n/k%2 : ℕ) : ℤ) = 1 := by omega
  have hpar : (2 : ℤ)*(k/2 : ℕ)+(k%2 : ℕ) = k := by omega
  have hstrict : (2 : ℤ)*(n/k/2 : ℕ)+(n/k%2 : ℕ) = k+2 → ((k : ℕ) : ℤ)%2 < (n%k : ℕ) := by
    intro he
    have hq : n/k = k+2 := by omega
    have := hquot.2 hq
    omega
  obtain ⟨B, hB⟩ := high_offset_exists hk a hex hhigh
  have hs : 1 ≤ (a : ℤ)-(n/k/2 : ℕ) := by omega
  have hh : (1 : ℤ) ≤ (k/2 : ℕ) := by omega
  have hdata := high_offset_data k (n/k/2 : ℕ) (n/k%2 : ℕ) (n%k : ℕ)
    ((a : ℤ)-(n/k/2 : ℕ)) B (by omega) heps (by omega) (by omega)
    (by omega) hstrict hs hB
  have houter := PetersenTables.high_offset_outer (k/2 : ℕ) (k%2 : ℕ) (n/k/2 : ℕ)
    (n/k%2 : ℕ) (n%k : ℕ) ((a : ℤ)-(n/k/2 : ℕ)) B hh hkp (by omega) heps
    (by omega) (by omega) (by omega) (by intro he; have := hstrict (by omega); omega) hs (by simpa only [hpar] using hB)
  have hbr : -(k : ℤ) ≤ B ∧ -(k : ℤ) ≤ (n%k : ℕ)-B := by
    rcases hB with ho | ho | ho | ho | ho <;> omega
  have hT : (2 : ℤ)*(n/k/2 : ℕ) ≤ 2*((n/k+H k (n%k))/2 : ℕ) := by omega
  apply central_witness hk hmetric (n/k/2 : ℕ) (n/k%2 : ℕ) (n%k : ℕ) B a hqn rfl hbr.1 hbr.2
    (by linarith only [hdata.1]) (by omega) (hdata.2.1.trans hT) (hdata.2.2.1.trans hT)
    hdata.2.2.2.1 hdata.2.2.2.2.1 hdata.2.2.2.2.2 houter

end Petersen
```

### `PetersenMiddle.lean`

```lean
import PetersenHighWitness
import PetersenLowWitness
import PetersenRadii

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- The generic-range witness, with no arithmetic or table assumptions. -/
theorem witness_middle (hk : 3 ≤ k) (hn : nk k < n) (a : ℕ)
    (ha : 2 ≤ a) (hex : ∃ j : ZMod n, f n k j = a) :
    ∃ j : ZMod n, f n k j = a ∧ outerCount n k j ≤ 3 ∧ 4 ≤ innerCount n k j := by
  by_cases hlow : a ≤ (n/k)/2
  · exact ⟨((a*k : ℕ) : ZMod n), witness_low hk (threshold_metric (by omega) hn) a ha hlow⟩
  · exact witness_high hk hn a (by omega) hex

theorem middle_strict_imbalance (hk : 3 ≤ k) (hn : nk k < n) (a : ℕ)
    (ha : 2 ≤ a) (hex : ∃ j : ZMod n, f n k j = a) :
    ∃ j : ZMod n, f n k j = a ∧ imbalance n k j < 0 := by
  obtain ⟨j, hj, ho, hi⟩ := witness_middle hk hn a ha hex
  refine ⟨j, hj, ?_⟩
  rw [cancellation (by omega) (threshold_metric (by omega) hn)]
  omega

/-- The main clause for every generic subdiametral distance ell>=3.
The two boundary distances and k=2 are deliberately not included. -/
theorem generic_not_LDB (hk : 3 ≤ k) (hn : nk k < n) (ell : ℕ)
    (h3 : 3 ≤ ell) (hD : ell < (GP n k).diam) : ¬ LDB (GP n k) ell := by
  have hm := threshold_metric (by omega : 2 ≤ k) hn
  obtain ⟨j, hj, ho, hi⟩ := witness_middle hk hn (ell-1) (by omega)
    (subdiam_radius (by omega) hm ell (by omega) hD)
  have h := strict_imbalance_of_counts (by omega : 2 ≤ k) hm j (by omega)
  simpa only [hj, Nat.sub_add_cancel (by omega : 1 ≤ ell)] using h

/-- Fully quantified generic portion of the review's second conjunct. -/
theorem generic_eventual_nonbalance :
    ∀ k (_hk : 3 ≤ k), ∀ n (hn : nk k < n),
      letI : NeZero n := ⟨by omega⟩
      ∀ ell, 3 ≤ ell → ell < (GP n k).diam → ¬ LDB (GP n k) ell := by
  intro k hk n hn
  let : NeZero n := ⟨by omega⟩
  exact generic_not_LDB hk hn

end Petersen
```

### `PetersenStageThreeAudit.lean`

```lean
import PetersenMiddle

#print axioms Petersen.outerCount_le_signedU
#print axioms Petersen.innerCount_four_lifts
#print axioms Petersen.low_outer
#print axioms Petersen.witness_low
#print axioms Petersen.low_strict_imbalance
#print axioms Petersen.low_not_LDB
#print axioms Petersen.attained_cost_bound
#print axioms Petersen.central_witness
#print axioms PetersenTables.high_offset_outer
#print axioms Petersen.high_offset_data
#print axioms Petersen.high_offset_exists
#print axioms Petersen.witness_high
#print axioms Petersen.witness_middle
#print axioms Petersen.middle_strict_imbalance
#print axioms Petersen.generic_not_LDB
#print axioms Petersen.generic_eventual_nonbalance
#check Petersen.generic_eventual_nonbalance
```

### `PetersenBoundaryOuter.lean`

```lean
import PetersenOuterBridge

set_option linter.unusedSimpArgs false

namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The full outer count at a spoke, including its origin. -/
theorem outer_zero (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) :
    outerCount n k 0 = 2*(k : ℤ)+4 := by
  rw [outerCount_strip hk hn, sum_symmetric]
  have hm : 2*(k/2+1) < n := by
    have := Nat.mod_add_div k 2
    have hm : 2*(k/2+1) ≤ k+2 := by omega
    nlinarith
  have hv (t : ℤ) (ht : 1 ≤ t) (htm : t ≤ (k/2+1 : ℕ)) :
      pulse t.natAbs (H k t.natAbs+2) (f n k (t : ZMod n)+1) =
        2 - if k%2 = 0 ∧ t = (k/2+1 : ℕ) then 1 else 0 := by
    have hab : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have hp := p_intCast_strip hm t (by rw [abs_of_nonneg (by omega)]; exact htm)
    have hf := (outer_shortcut_values hk hn (t : ZMod n) (by rw [hp]; omega)).2
    rw [hf, hp]
    have hH : (H k t.natAbs : ℤ) = min t ((k : ℤ)+1-t) := by
      unfold H
      rw [Nat.cast_min, Nat.cast_sub (by omega : t.natAbs ≤ k+1)]
      push_cast
      rw [abs_of_nonneg (by omega : 0 ≤ t)]
    simp only [hH, hab, pulse, sign]
    split_ifs <;> omega
  have hs : (∑ t ∈ Finset.Icc 1 ((k/2+1 : ℕ) : ℤ),
      (pulse (-t).natAbs (H k (-t).natAbs+2) (f n k ((-t : ℤ) : ZMod n)+1) +
       pulse t.natAbs (H k t.natAbs+2) (f n k (t : ZMod n)+1))) =
      ∑ t ∈ Finset.Icc 1 ((k/2+1 : ℕ) : ℤ),
        (4 - if k%2 = 0 ∧ t = (k/2+1 : ℕ) then 2 else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hb := Finset.mem_Icc.mp ht
    rw [Int.natAbs_neg, Int.cast_neg, f_neg (by omega) hn, hv t hb.1 hb.2]
    split_ifs <;> omega
  simp only [sub_zero, Int.cast_neg] at *
  rw [hs]
  have hz : pulse (0 : ℤ) (H k 0+2) (f n k (0 : ZMod n)+1) = 2 := by
    rw [f_zero (by omega) hn]; norm_num [H, pulse, sign]
  simp only [Int.natAbs_zero, Int.cast_zero, hz]
  rw [Finset.sum_sub_distrib]
  by_cases he : k%2 = 0
  · simp only [he, true_and]
    simp [Finset.sum_ite_eq', Finset.mem_Icc, show (1 : ℤ) ≤ (k/2+1 : ℕ) by omega]
    omega
  · simp only [he, false_and, ite_false, Finset.sum_const_zero, sub_zero]
    simp
    omega

end Petersen
```

### `PetersenRayInjection.lean`

```lean
import PetersenInnerArithmetic
import PetersenOuterSum

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- When k does not divide n, two short inner rays are disjoint, even if
 their combined index width exceeds n. -/
theorem inner_route_injective (hk : 0 < k) (hr : n%k ≠ 0)
    {a b : ℤ} (hw : (k : ℤ)*|a-b| < 2*n)
    (he : (k : ZMod n)*(a : ZMod n) = (k : ZMod n)*(b : ZMod n)) : a = b := by
  have hn : 0 < n := NeZero.pos n
  have hz : (((k : ℤ)*(a-b) : ℤ) : ZMod n) = 0 := by push_cast; rw [mul_sub, he]; simp
  obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have ha : |(k : ℤ)*(a-b)| < 2*n := by
    rw [abs_mul, abs_of_nonneg (by omega : 0 ≤ (k : ℤ))]; exact hw
  have hdabs : |d| < 2 := by
    rw [hd, abs_mul, abs_of_nonneg (by omega : 0 ≤ (n : ℤ))] at ha
    nlinarith
  have hd0 : d = 0 := by
    by_contra h
    have heq : d = 1 ∨ d = -1 := by rw [abs_lt] at hdabs; omega
    have hdiv : (k : ℤ) ∣ (n : ℤ) := by
      rcases heq with rfl | rfl
      · exact ⟨a-b, by nlinarith [hd]⟩
      · exact ⟨b-a, by nlinarith [hd]⟩
    have hdivn : k ∣ n := by exact_mod_cast hdiv
    exact hr (Nat.mod_eq_zero_of_dvd hdivn)
  rw [hd0] at hd
  nlinarith

omit [NeZero n] in
/-- A shorter width than n works without any divisibility restriction. -/
theorem inner_route_injective_short (hk : 0 < k)
    {a b : ℤ} (hw : (k : ℤ)*|a-b| < n)
    (he : (k : ZMod n)*(a : ZMod n) = (k : ZMod n)*(b : ZMod n)) : a = b := by
  have hz : (((k : ℤ)*(a-b) : ℤ) : ZMod n) = 0 := by push_cast; rw [mul_sub, he]; simp
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have ha : |(k : ℤ)*(a-b)| < n := by
    rw [abs_mul, abs_of_nonneg (by omega : 0 ≤ (k : ℤ))]; exact hw
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    (Int.ofNat_lt.mp (by simpa only [Int.natCast_natAbs, Int.natAbs_natCast] using ha))
  nlinarith

/-- The full-deficit profile on signed inner rays. -/
theorem f_signed_inner (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (z : ℤ)
    (hq : z.natAbs ≤ n/k) (hT : 2*z.natAbs ≤ n/k+H k (n%k)) :
    f n k ((k : ZMod n)*(z : ZMod n)) = z.natAbs := by
  have hf := f_inner_full hk hn z.natAbs hq hT
  by_cases hz : 0 ≤ z
  · have he : ((z.natAbs : ℕ) : ZMod n) = (z : ZMod n) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hz]
    simpa only [Nat.cast_mul, he] using hf
  · have he : ((z.natAbs : ℕ) : ZMod n) = -(z : ZMod n) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg (by omega), Int.cast_neg]
    simpa only [Nat.cast_mul, he, mul_neg, f_neg hk hn] using hf

end Petersen
```

### `PetersenBoundaryInner.lean`

```lean
import PetersenRayInjection
import PetersenArithmetic

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- A finite interval of full inner deficits contributes two per position at j=0. -/
theorem inner_zero_interval (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (L U : ℤ)
    (hinj : ∀ a ∈ Finset.Icc L U, ∀ b ∈ Finset.Icc L U,
      (k : ZMod n)*(a : ZMod n) = (k : ZMod n)*(b : ZMod n) → a = b)
    (hfull : ∀ z ∈ Finset.Icc L U, z.natAbs ≤ n/k ∧
      2*z.natAbs ≤ n/k+H k (n%k)) :
    2*((U-L+1).toNat : ℤ) ≤ innerCount n k 0 := by
  classical
  let s := Finset.Icc L U
  have hs := innerCount_selected (k := k) (0 : ZMod n)
    (fun z : ↥s => (k : ZMod n)*(z.val : ZMod n))
    (by intro a b h; exact Subtype.ext (hinj a.val a.property b.val b.property h))
  have hw : ∀ z : ↥s, (2 : ℤ) ≤ innerPulse n k 0 ((k : ZMod n)*(z.val : ZMod n)) := by
    intro z
    have hb := hfull z.val z.property
    have hf := f_signed_inner hk hn z.val hb.1 hb.2
    have h := innerPulse_route hk hn (0 : ZMod n) z.val hf
    simpa [zero_sub, f_neg hk hn, hf, K] using h
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hw z)
  have hc : Fintype.card ↥s = (U-L+1).toNat := by simp [s]; congr 1; omega
  simpa only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul, mul_comm] using hh.trans hs

/-- Sufficient full-ray bound, with the r=0 antipode counted only once. -/
theorem inner_zero_lower (hk : 3 ≤ k) (hn : nk k < n) :
    2*(k : ℤ)+4 < innerCount n k 0 := by
  have hm := threshold_metric (by omega : 2 ≤ k) hn
  have hq := (threshold_quotient hk).mp hn
  have hr := Nat.mod_lt n (by omega : 0 < k)
  have hd := Nat.div_add_mod n k
  have hH : H k (n%k) ≤ (k+1)/2 := by unfold H; omega
  by_cases hz : n%k = 0
  · have hq' : k+3 ≤ n/k := by have := hq.2; omega
    let L : ℤ := -(((n/k : ℕ) : ℤ)/2)
    let U : ℤ := ((n/k : ℕ) : ℤ)-1-((n/k : ℕ) : ℤ)/2
    have hsum := inner_zero_interval (by omega : 2 ≤ k) hm L U
      (by
        intro a ha b hb he
        have ha' := Finset.mem_Icc.mp ha
        have hb' := Finset.mem_Icc.mp hb
        apply inner_route_injective_short (by omega : 0 < k) _ he
        have hab : |a-b| ≤ (n/k : ℕ)-1 := by dsimp [L, U] at *; rw [abs_le]; omega
        have hmul := mul_le_mul_of_nonneg_left hab (show (0 : ℤ) ≤ k by omega)
        have hdi : (n : ℤ) = (n/k : ℕ)*(k : ℤ) := by exact_mod_cast (by simpa [hz, Nat.mul_comm] using hd.symm : n = n/k*k)
        nlinarith)
      (by
        intro z hmem
        have hb := Finset.mem_Icc.mp hmem
        have ha : |z| ≤ ((n/k : ℕ) : ℤ)/2 := by dsimp [L, U] at *; rw [abs_le]; omega
        have ha' : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
        simp only [hz, H, add_zero]
        constructor <;> omega)
    have hc : (U-L+1).toNat = n/k := by dsimp [L, U]; omega
    rw [hc] at hsum
    omega
  · let T : ℕ := (n/k+H k (n%k))/2
    have hTq : T < n/k := by dsimp [T]; omega
    have hsum := inner_zero_interval (by omega : 2 ≤ k) hm (-(T : ℤ)) T
      (by
        intro a ha b hb he
        have ha' := Finset.mem_Icc.mp ha
        have hb' := Finset.mem_Icc.mp hb
        apply inner_route_injective (by omega : 0 < k) hz _ he
        have hab : |a-b| ≤ 2*(T : ℤ) := by rw [abs_le]; omega
        have hmul := mul_le_mul_of_nonneg_left hab (show (0 : ℤ) ≤ k by omega)
        have hT : (T : ℤ) < (n/k : ℕ) := by exact_mod_cast hTq
        have hdi : (n/k : ℕ)*(k : ℤ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n k
        nlinarith)
      (by
        intro z hmem
        have hb := Finset.mem_Icc.mp hmem
        have ha : |z| ≤ (T : ℤ) := by rw [abs_le]; omega
        have ha' : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
        dsimp [T] at *
        constructor <;> omega)
    have hc : (((T : ℤ)-(-(T : ℤ))+1).toNat : ℤ) = 2*T+1 := by omega
    rw [hc] at hsum
    have hHp : 1 ≤ H k (n%k) := by unfold H; omega
    have hex : 2*(k : ℤ)+4 < 2*(2*(T : ℤ)+1) := by
      dsimp [T]
      have hh := hq.2
      omega
    omega

end Petersen
```

### `PetersenBoundaryOneOuter.lean`

```lean
import PetersenBoundaryOuter

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

private theorem f_one_strip (hk : 3 ≤ k) (hn : k*(k+2) ≤ n)
    (t : ℤ) (ht : |t| ≤ (k/2+1 : ℕ)) :
    (f n k (((k : ℤ)+t : ℤ) : ZMod n) : ℤ) = 1+g k t := by
  have ht' := abs_le.mp ht
  have htk : t ≤ (k : ℤ) := by omega
  have hg := localG_eq_g k t (by omega) (by omega) (by omega)
  have hcost : 0 ≤ 1+g k t ∧ 1+g k t ≤ k := by
    rw [← hg]; unfold PetersenTables.localG; split_ifs <;> omega
  have hx : 0 ≤ (k : ℤ)+t := by omega
  have hxn : (k : ℤ)+t < n := by
    have hni : (k : ℤ)*(k+2) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [f_int_lift (by omega) _ hx hxn,
    show (k : ℤ)+t = 1*k+t by ring, g_translate _ _ _ (by omega)]
  simp only [one_mul]
  have hy : 0 ≤ (n : ℤ)-(k+t) := by omega
  have hnat : (((n : ℤ)-(k+t)).toNat : ℤ) = (n : ℤ)-(k+t) := Int.toNat_of_nonneg hy
  have hl := lineCost_displacement (by omega : 2 ≤ k) ((n : ℤ)-(k+t)).toNat
  have hli : (n : ℤ)-(k+t) ≤ k*g k ((n : ℤ)-(k+t)) := by
    have h := Int.ofNat_le.mpr hl
    rw [Nat.cast_mul, ← g_nat k _ (by omega), hnat] at h
    exact h
  have hni : (k : ℤ)*(k+2) ≤ n := by exact_mod_cast hn
  apply min_eq_left
  by_contra h
  have hh : g k ((n : ℤ)-(k+t)) ≤ k-1 := by omega
  nlinarith

/-- Exact outer count at the inner-edge index k. -/
theorem outer_one (hk : 3 ≤ k) (hn : k*(k+2) ≤ n) :
    outerCount n k (k : ZMod n) = (k : ℤ)+3-k%2 := by
  rw [outerCount_strip hk hn, sum_symmetric]
  have hv (t : ℤ) (ht : 1 ≤ t) (htm : t ≤ (k/2+1 : ℕ)) :
      pulse (-t).natAbs (H k (-t).natAbs+2) (f n k (((-t : ℤ) : ZMod n)-(k : ZMod n))+1) +
      pulse t.natAbs (H k t.natAbs+2) (f n k ((t : ZMod n)-(k : ZMod n))+1) =
        2 + (if k%2 = 0 ∧ t = (k/2 : ℕ) then 1 else 0) -
          (if k%2 = 0 ∧ t = (k/2+1 : ℕ) then 1 else 0) := by
    have hab : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have hH : (H k t.natAbs : ℤ) = min t ((k : ℤ)+1-t) := by
      unfold H
      rw [Nat.cast_min, Nat.cast_sub (by omega : t.natAbs ≤ k+1)]
      push_cast
      rw [abs_of_nonneg (by omega : 0 ≤ t)]
    have he1 : ((-t : ℤ) : ZMod n)-(k : ZMod n) = -(((k : ℤ)+t : ℤ) : ZMod n) := by push_cast; ring
    have he2 : (t : ZMod n)-(k : ZMod n) = -(((k : ℤ)+(-t) : ℤ) : ZMod n) := by push_cast; ring
    rw [he1, he2, f_neg (by omega) hn, f_neg (by omega) hn]
    have hpos := f_one_strip hk hn t (by rw [abs_of_nonneg (by omega)]; exact htm)
    have hneg := f_one_strip hk hn (-t) (by rw [abs_neg, abs_of_nonneg (by omega)]; exact htm)
    have hgp := localG_eq_g k t (by omega) (by omega) (by omega)
    have hgn := localG_eq_g k (-t) (by omega) (by omega) (by omega)
    have hgp' : g k t = min t ((k : ℤ)+1-t) := by
      rw [← hgp]; unfold PetersenTables.localG; split_ifs <;> omega
    have hgn' : g k (-t) = min t ((k : ℤ)-1-t) := by
      rw [← hgn]; unfold PetersenTables.localG; split_ifs <;> omega
    simp only [Int.natAbs_neg, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hpos, hneg, hab, hH, hgp', hgn']
    unfold pulse sign
    split_ifs <;> omega
  have hz : pulse (0 : ℤ) (H k 0+2) (f n k ((0 : ZMod n)-(k : ZMod n))+1) = 1 := by
    rw [zero_sub, f_neg (by omega) hn]
    have h := f_one_strip hk hn 0 (by simp; omega)
    have hf : f n k (k : ZMod n) = 1 := by
      have hg0 : g k 0 = 0 := by simp [g, min_eq_left (by omega : (0 : ℤ) ≤ k+1)]
      simp only [add_zero, hg0, add_zero, Int.cast_natCast] at h
      omega
    rw [hf]; norm_num [H, pulse, sign]
  simp only [Int.natAbs_zero, Int.cast_zero, Nat.cast_zero]
  rw [show pulse (0 : ℤ) (H k 0+2) (f n k ((0 : ZMod n)-(k : ZMod n))+1) = 1 from hz]
  have hs : (∑ t ∈ Finset.Icc 1 ((k/2+1 : ℕ) : ℤ),
      (pulse (-t).natAbs (H k (-t).natAbs+2) (f n k (((-t : ℤ) : ZMod n)-(k : ZMod n))+1) +
       pulse t.natAbs (H k t.natAbs+2) (f n k ((t : ZMod n)-(k : ZMod n))+1))) =
      ∑ t ∈ Finset.Icc 1 ((k/2+1 : ℕ) : ℤ),
        (2 + (if k%2 = 0 ∧ t = (k/2 : ℕ) then 1 else 0) -
          (if k%2 = 0 ∧ t = (k/2+1 : ℕ) then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hv t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
  rw [hs, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  by_cases he : k%2 = 0
  · simp [he, Finset.sum_ite_eq', Finset.mem_Icc, show 1 ≤ k/2 by omega]
    omega
  · simp [he]
    omega

end Petersen
```

### `PetersenBoundaryOneInner.lean`

```lean
import PetersenBoundaryInner

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

private theorem signed_ray_value (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (z : ℤ) (hq : z.natAbs ≤ n/k) :
    (f n k ((k : ZMod n)*(z : ZMod n)) : ℤ) =
      min |z| ((n/k : ℕ)+H k (n%k)-|z|) := by
  have hf := f_inner_multiple hk hn z.natAbs hq
  have hf' : f n k ((k : ZMod n)*(z : ZMod n)) =
      min z.natAbs (n/k-z.natAbs+H k (n%k)) := by
    by_cases hz : 0 ≤ z
    · have he : ((z.natAbs : ℕ) : ZMod n) = (z : ZMod n) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hz]
      simpa only [Nat.cast_mul, he] using hf
    · have he : ((z.natAbs : ℕ) : ZMod n) = -(z : ZMod n) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg (by omega), Int.cast_neg]
      simpa only [Nat.cast_mul, he, mul_neg, f_neg hk hn] using hf
  rw [hf', Nat.cast_min, Nat.cast_add, Nat.cast_sub hq, Int.natCast_natAbs]
  congr 1
  ring

private theorem one_ray_weight (S z : ℤ) (hS : 4 ≤ S)
    (hz : -(S/2) ≤ z) (hz' : z ≤ S/2) :
    K (min |1-z| (S-|1-z|)-|z|) =
      1 + if S%2 = 1 ∧ z = -(S/2) then 1 else 0 := by
  unfold K
  rw [abs_sub_comm 1 z]
  rcases le_total 0 z with hp | hp
  · rw [abs_of_nonneg hp]
    by_cases h1 : 1 ≤ z
    · rw [abs_of_nonneg (by omega : 0 ≤ z-1)]; split_ifs <;> omega
    · have he : z = 0 := by omega
      subst z; norm_num; split_ifs <;> omega
  · rw [abs_of_nonpos hp, abs_of_nonpos (by omega : z-1 ≤ 0)]
    split_ifs <;> omega

/-- Radius-one lower bound from a selected interval; the odd terminal unit is retained. -/
theorem inner_one_interval (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (L U : ℤ)
    (hS : 4 ≤ (n/k+H k (n%k) : ℕ))
    (hL : -(((n/k+H k (n%k) : ℕ) : ℤ)/2) = L)
    (hU : L ≤ U) (hUp : U ≤ ((n/k+H k (n%k) : ℕ) : ℤ)/2)
    (hinj : ∀ a ∈ Finset.Icc L U, ∀ b ∈ Finset.Icc L U,
      (k : ZMod n)*(a : ZMod n) = (k : ZMod n)*(b : ZMod n) → a = b)
    (hfull : ∀ z ∈ Finset.Icc L U, z.natAbs ≤ n/k ∧
      2*z.natAbs ≤ n/k+H k (n%k) ∧ (1-z).natAbs ≤ n/k) :
    ((U-L+1).toNat : ℤ) + ((n/k+H k (n%k))%2 : ℕ) ≤
      innerCount n k (k : ZMod n) := by
  classical
  let s := Finset.Icc L U
  let S : ℤ := (n/k+H k (n%k) : ℕ)
  have hs := innerCount_selected (k := k) (k : ZMod n)
    (fun z : ↥s => (k : ZMod n)*(z.val : ZMod n))
    (by intro a b h; exact Subtype.ext (hinj a.val a.property b.val b.property h))
  have hw (z : ↥s) :
      1+(if S%2 = 1 ∧ z.val = L then 1 else 0 : ℤ) ≤
        innerPulse n k (k : ZMod n) ((k : ZMod n)*(z.val : ZMod n)) := by
    have hb := hfull z.val z.property
    have hf := f_signed_inner hk hn z.val hb.1 hb.2.1
    have h := innerPulse_route hk hn (k : ZMod n) z.val hf
    have he : (k : ZMod n)-(k : ZMod n)*(z.val : ZMod n) =
        (k : ZMod n)*((1-z.val : ℤ) : ZMod n) := by push_cast; ring
    rw [he, signed_ray_value hk hn _ hb.2.2, Int.natCast_natAbs] at h
    have hz := Finset.mem_Icc.mp z.property
    have hw := one_ray_weight S z.val (by dsimp [S]; exact_mod_cast hS) (by dsimp [S]; omega) (by dsimp [S]; omega)
    dsimp [S] at *
    rw [hw] at h
    simpa only [hL] using h
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hw z)
  have hc : Fintype.card ↥s = (U-L+1).toNat := by simp [s]; congr 1; omega
  have hsum : (∑ z : ↥s, (1+(if S%2 = 1 ∧ z.val = L then 1 else 0 : ℤ))) =
      ((U-L+1).toNat : ℤ)+(S%2) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul, mul_one]
    change _ + (∑ z : ↥s, (fun t : ℤ => if S%2 = 1 ∧ t = L then (1 : ℤ) else 0) z.val) = _
    rw [Finset.sum_coe_sort s (fun t : ℤ => if S%2 = 1 ∧ t = L then (1 : ℤ) else 0)]
    by_cases he : S%2 = 1
    · simp [he, s, Finset.mem_Icc, hU]
    · have he0 : S%2 = 0 := by omega
      simp [he, he0]
  rw [hsum] at hh
  convert hh.trans hs using 1; simp [S, Nat.cast_add, Int.natCast_emod]

end Petersen
```

### `PetersenBoundaryOneLower.lean`

```lean
import PetersenBoundaryOneInner

set_option linter.unusedSimpArgs false
namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem inner_one_lower (hk : 3 ≤ k) (hn : nk k < n) :
    (k : ℤ)+3-k%2 < innerCount n k (k : ZMod n) := by
  have hm := threshold_metric (by omega : 2 ≤ k) hn
  have hq := (threshold_quotient hk).mp hn
  have hr := Nat.mod_lt n (by omega : 0 < k)
  have hd := Nat.div_add_mod n k
  have hH : H k (n%k) ≤ (k+1)/2 := by unfold H; omega
  by_cases hz : n%k = 0
  · have hq' : k+3 ≤ n/k := by have := hq.2; omega
    let L : ℤ := -(((n/k : ℕ) : ℤ)/2)
    let U : ℤ := ((n/k : ℕ) : ℤ)-1-((n/k : ℕ) : ℤ)/2
    have hsum := inner_one_interval (by omega : 2 ≤ k) hm L U
      (by omega) (by simp [hz, H, L]) (by dsimp [L, U]; omega) (by dsimp [U]; simp [hz, H]; omega)
      (by
        intro a ha b hb he
        have ha' := Finset.mem_Icc.mp ha
        have hb' := Finset.mem_Icc.mp hb
        apply inner_route_injective_short (by omega : 0 < k) _ he
        have hab : |a-b| ≤ (n/k : ℕ)-1 := by dsimp [L, U] at *; rw [abs_le]; omega
        have hmul := mul_le_mul_of_nonneg_left hab (show (0 : ℤ) ≤ k by omega)
        have hdi : (n : ℤ) = (n/k : ℕ)*(k : ℤ) := by exact_mod_cast (by simpa [hz, Nat.mul_comm] using hd.symm : n = n/k*k)
        nlinarith)
      (by
        intro z hmem
        have hb := Finset.mem_Icc.mp hmem
        have ha : |z| ≤ ((n/k : ℕ) : ℤ)/2 := by dsimp [L, U] at *; rw [abs_le]; omega
        have ha' : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
        simp only [hz, H, add_zero]
        refine ⟨by omega, by omega, ?_⟩
        have habs : (1-z).natAbs ≤ z.natAbs+1 := by
          have := abs_sub (1 : ℤ) z
          rw [Int.natCast_natAbs] at ha'
          have := Int.natCast_natAbs (1-z)
          omega
        omega)
    have hc : (U-L+1).toNat = n/k := by dsimp [L, U]; omega
    rw [hc] at hsum
    simp only [hz, H, add_zero] at hsum
    omega
  · let T : ℕ := (n/k+H k (n%k))/2
    have hTq : T < n/k := by dsimp [T]; try omega
    have hsum := inner_one_interval (by omega : 2 ≤ k) hm (-(T : ℤ)) T
      (by omega) (by dsimp [T]; try omega) (by omega) (by dsimp [T]; try omega)
      (by
        intro a ha b hb he
        have ha' := Finset.mem_Icc.mp ha
        have hb' := Finset.mem_Icc.mp hb
        apply inner_route_injective (by omega : 0 < k) hz _ he
        have hab : |a-b| ≤ 2*(T : ℤ) := by rw [abs_le]; omega
        have hmul := mul_le_mul_of_nonneg_left hab (show (0 : ℤ) ≤ k by omega)
        have hT : (T : ℤ) < (n/k : ℕ) := by exact_mod_cast hTq
        have hdi : (n/k : ℕ)*(k : ℤ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n k
        nlinarith)
      (by
        intro z hmem
        have hb := Finset.mem_Icc.mp hmem
        have ha : |z| ≤ (T : ℤ) := by rw [abs_le]; omega
        have ha' : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
        dsimp [T] at *
        refine ⟨by omega, by omega, ?_⟩
        have habs : (1-z).natAbs ≤ z.natAbs+1 := by
          have := abs_sub (1 : ℤ) z
          rw [Int.natCast_natAbs] at ha'
          have := Int.natCast_natAbs (1-z)
          omega
        omega)
    have hc : (((T : ℤ)-(-(T : ℤ))+1).toNat : ℤ) = 2*T+1 := by omega
    rw [hc] at hsum
    have hHp : 1 ≤ H k (n%k) := by unfold H; omega
    have hh := hq.2
    dsimp [T] at hsum
    omega

end Petersen
```

### `PetersenLarge.lean`

```lean
import PetersenBoundaryOneOuter
import PetersenBoundaryOneLower
import PetersenMiddle

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem witness_zero (hk : 3 ≤ k) (hn : nk k < n) : imbalance n k 0 < 0 := by
  have hm := threshold_metric (by omega : 2 ≤ k) hn
  rw [cancellation (by omega) hm, outer_zero hk hm]
  have := inner_zero_lower hk hn
  omega

theorem witness_one (hk : 3 ≤ k) (hn : nk k < n) :
    f n k (k : ZMod n) = 1 ∧ imbalance n k (k : ZMod n) < 0 := by
  have hm := threshold_metric (by omega : 2 ≤ k) hn
  constructor
  · have hf := f_inner_full (by omega : 2 ≤ k) hm 1
      (by have := (threshold_quotient hk).mp hn; omega)
      (by have := (threshold_quotient hk).mp hn; omega)
    simpa only [mul_one, Nat.cast_one] using hf
  · rw [cancellation (by omega) hm, outer_one hk hm]
    have := inner_one_lower hk hn
    omega

/-- Complete nonbalance clause for all k≥3 and all subdiametral distances. -/
theorem main_large (hk : 3 ≤ k) (hn : nk k < n) (ell : ℕ)
    (h1 : 1 ≤ ell) (hD : ell < (GP n k).diam) : ¬ LDB (GP n k) ell := by
  have hm := threshold_metric (by omega : 2 ≤ k) hn
  by_cases he : ell = 1
  · subst ell
    have h := not_LDB_of_imbalance (by omega : 2 ≤ k) hm 0 (ne_of_lt (witness_zero hk hn))
    simpa only [f_zero (by omega) hm, zero_add] using h
  · by_cases he2 : ell = 2
    · subst ell
      have hw := witness_one hk hn
      have h := not_LDB_of_imbalance (by omega : 2 ≤ k) hm (k : ZMod n) (ne_of_lt hw.2)
      simpa only [hw.1] using h
    · exact generic_not_LDB hk hn ell (by omega) hD

theorem large_eventual_nonbalance :
    ∀ k (_hk : 3 ≤ k), ∀ n (hn : nk k < n),
      let : NeZero n := ⟨by omega⟩
      ∀ ell, 1 ≤ ell → ell < (GP n k).diam → ¬ LDB (GP n k) ell := by
  intro k hk n hn
  let : NeZero n := ⟨by omega⟩
  exact main_large hk hn

#print axioms witness_zero
#print axioms witness_one
#print axioms main_large
#print axioms large_eventual_nonbalance
#print large_eventual_nonbalance
end Petersen
```

### `PetersenLowInnerExtended.lean`

```lean
import PetersenInnerWitness

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- All low radii share the same inner counting argument. -/
theorem low_inner_extended (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (a : ℕ)
    (ha : 2 ≤ a) (haq : a ≤ (n/k)/2) :
    f n k (((a*k : ℕ) : ZMod n)) = a ∧
      4 ≤ innerCount n k (((a*k : ℕ) : ZMod n)) := by
  have hk0 : 0 < k := by omega
  have hq : k+2 ≤ n/k := (Nat.le_div_iff_mul_le hk0).mpr (by nlinarith)
  have hr := Nat.mod_lt n hk0
  have hd := Nat.div_add_mod n k
  have hH : 2*H k (n%k) ≤ k+1 := by unfold H; omega
  have hHq : H k (n%k) ≤ n/k-a := by omega
  have haqn : a ≤ n/k := by omega
  have hrem : n/k-a+a = n/k := Nat.sub_add_cancel haqn
  have hmul : (n/k-a)*k+a*k = (n/k)*k := by rw [← Nat.add_mul, hrem]
  have hs : n = (a*k+0)+((n/k-a)*k+n%k) := by nlinarith only [hmul, hd]
  have hj : a*k+0 < n := by
    have hm := Nat.mul_le_mul_right k (show a+1 ≤ n/k by omega)
    have hqkn : n/k*k ≤ n := Nat.div_mul_le_self n k
    have hmk : a*k < (a+1)*k := Nat.mul_lt_mul_of_pos_right (by omega) hk0
    exact lt_of_lt_of_le hmk (hm.trans hqkn)
  have hjp : (n/k-a)*k+n%k < n := by nlinarith [hs]
  have hC : a ≤ 2*((n/k+H k (n%k))/2) := by omega
  have hCp : n/k-a+H k (n%k) ≤ 2*((n/k+H k (n%k))/2) := by omega
  have hwidth : (k : ℤ)*(((a : ℤ)+1)/2+(((n/k-a+H k (n%k) : ℕ) : ℤ)+1)/2) < n := by
    have hi : ((a : ℤ)+1)/2+(((n/k-a+H k (n%k) : ℕ) : ℤ)+1)/2 < n/k := by
      omega
    have hqi : (k : ℤ)*(n/k : ℕ) ≤ n := by exact_mod_cast (by omega : k*(n/k) ≤ n)
    have hm := mul_lt_mul_of_pos_left hi (show (0 : ℤ) < k by omega)
    exact lt_of_lt_of_le hm hqi
  constructor
  · rw [mul_comm a k, f_inner_multiple (by omega) hn a haqn, min_eq_left (by omega)]
  · have h := innerCount_four_blocks (by omega : 2 ≤ k) hn a 0 (n/k-a) (n%k)
      a (n/k-a+H k (n%k)) (by omega) hr (by simp [H]) rfl ha (by omega)
      (by simp [H]) hHq hj hjp hs hC hCp hwidth
    simpa only [add_zero] using h

end Petersen
```

### `PetersenK2Metric.lean`

```lean
import PetersenInnerLifts
import PetersenOuterBridge

namespace Petersen
variable {n : ℕ} [NeZero n]

theorem lineCost_two (x : ℕ) : lineCost 2 x = (x+1)/2 := by
  unfold lineCost H
  omega

theorem f_two_near (j : ZMod n) : f n 2 j = (p n j+1)/2 := by
  unfold f p
  rw [lineCost_two, lineCost_two]
  omega

theorem f_two_lift (hn : 8 ≤ n) (x : ℤ) (hx : |x| < n) :
    (f n 2 (x : ZMod n) : ℤ) = min ((|x|+1)/2) (((n : ℤ)-|x|+1)/2) := by
  by_cases hp : 0 ≤ x
  · rw [f_int_lift (by decide) _ hp (by rw [abs_of_nonneg hp] at hx; exact hx)]
    have hg (y : ℤ) : g 2 y = (y+1)/2 := by unfold g; omega
    norm_num only [Nat.cast_ofNat]
    rw [hg, hg, abs_of_nonneg hp]
  · have he : (x : ZMod n) = -((-x : ℤ) : ZMod n) := by simp
    rw [he, f_neg (by decide : 2 ≤ 2) (by omega : 2*(2+2) ≤ n)]
    rw [f_int_lift (by decide) _ (by omega) (by rw [abs_of_neg (by omega)] at hx; exact hx)]
    have hg (y : ℤ) : g 2 y = (y+1)/2 := by unfold g; omega
    norm_num only [Nat.cast_ofNat]
    rw [hg, hg, abs_of_neg (by omega)]

/-- k=2 has a seven-position outer support. -/
theorem outer_two_strip (hn : 13 ≤ n) (j : ZMod n) :
    outerCount n 2 j = ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
      pulse z.natAbs ((z.natAbs+1)/2+2 : ℕ) (f n 2 ((z : ZMod n)-j)+1) := by
  have hsup (i : ZMod n) (hi : 3 < p n i) : outerPulse n 2 j i = 0 := by
    have hf := f_two_near i
    have he : outerProfile n 2 i = f n 2 i+2 := by unfold outerProfile; rw [hf]; omega
    simp [outerPulse, he, pulse]
  rw [outerCount_sum, sum_short_strip 3 (by omega) _ hsup]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : |z| ≤ (3 : ℕ) := by simpa only [Finset.mem_Icc, abs_le] using hz
  have hp := p_intCast_strip (show 2*3 < n by omega) z hz'
  have hf : f n 2 (z : ZMod n) = (z.natAbs+1)/2 := by rw [f_two_near, hp]
  have he : outerProfile n 2 (z : ZMod n) = z.natAbs := by
    unfold outerProfile
    rw [hp, hf]
    have hab : z.natAbs ≤ 3 := by have := Int.natCast_natAbs z; norm_num at hz'; omega
    omega
  simp only [outerPulse, he, hf, Nat.cast_add, Nat.cast_ofNat]

end Petersen
```

### `PetersenK2Tables.lean`

```lean
import PetersenUTableDefs
set_option maxHeartbeats 200000
namespace PetersenTables

def g2 (x : Int) := (x+1)/2

def k2term (z C s e : Int) : Int :=
  pulse s (g2 s+2) (1+C+g2 (z+e*s))

def U2 (z C : Int) : Int :=
  k2term z C 1 (-1) + k2term z C 1 1 +
  k2term z C 2 (-1) + k2term z C 2 1 +
  k2term z C 3 (-1) + k2term z C 3 1

theorem u2_zero (C : Int) (hc : 2 ≤ C) :
    U2 0 C = if C=2 ∨ C=3 then 2 else if C=4 then 1 else 0 := by
  dsimp only [U2,k2term,g2,pulse,sgn]
  omega

theorem u2_one (C : Int) (hc : 2 ≤ C) :
    U2 1 C = if C=2 then 2 else if C=3 ∨ C=4 then 1 else 0 := by
  dsimp only [U2,k2term,g2,pulse,sgn]
  omega

theorem u2_negative (C : Int) (hc : 4 ≤ C) :
    U2 (-1) C = if C=4 ∨ C=5 then 1 else 0 := by
  dsimp only [U2,k2term,g2,pulse,sgn]
  omega

theorem u2_low_bound (q r a : Int) (hq : 6 ≤ q)
    (hr : r=0 ∨ r=1) (ha : 2 ≤ a) (hQ : 2*a ≤ q)
    (hex : ¬ (q=6 ∧ r=0 ∧ a=3)) :
    U2 0 a + U2 r (q-a) ≤ 3 := by
  have hqa : 2 ≤ q-a := by omega
  rcases hr with hr | hr
  · subst r
    rw [u2_zero a ha, u2_zero (q-a) hqa]
    omega
  · subst r
    rw [u2_zero a ha, u2_one (q-a) hqa]
    omega

theorem u2_high_bound (Q r : Int) (hQ : 3 ≤ Q) (hr : r=0 ∨ r=1) :
    U2 1 Q + U2 (r-1) (Q+1) ≤ 2 := by
  rcases hr with hr | hr
  · subst r
    have h4 : 4 ≤ Q+1 := by omega
    rw [u2_one Q (by omega)]
    have hn : (0:Int)-1 = -1 := by omega
    rw [hn,u2_negative (Q+1) h4]
    omega
  · subst r
    rw [u2_one Q (by omega)]
    have hz : (1:Int)-1 = 0 := by omega
    rw [hz,u2_zero (Q+1) (by omega)]
    omega

#print axioms u2_low_bound
#print axioms u2_high_bound
end PetersenTables
```

### `PetersenK2Outer.lean`

```lean
import PetersenK2Metric
import PetersenK2Tables

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The same two-lift pulse bound, for the exceptional seven-position k=2 strip. -/
theorem outer_two_U (hn : 13 ≤ n) (A B Ap Bp : ℤ)
    (hj : 3 ≤ 2*A+B) (hjn : 2*A+B+3 < n)
    (hs : (n : ℤ) = (2*A+B)+(2*Ap+Bp))
    (hf : 2 ≤ f n 2 ((2*A+B : ℤ) : ZMod n)) :
    outerCount n 2 ((2*A+B : ℤ) : ZMod n) ≤
      PetersenTables.U2 B A + PetersenTables.U2 Bp Ap := by
  have hbranch (z : ℤ) (hz : |z| ≤ 3) :
      (f n 2 ((z : ZMod n)-((2*A+B : ℤ) : ZMod n)) : ℤ) =
        min (A+(B-z+1)/2) (Ap+(Bp+z+1)/2) := by
    have he : (z : ZMod n)-((2*A+B : ℤ) : ZMod n) =
        -(((2*A+B-z : ℤ) : ZMod n)) := by push_cast; ring
    rw [he, f_neg (by decide : 2 ≤ 2) (by omega : 2*(2+2) ≤ n),
      f_two_lift (by omega) _ (by rw [abs_le] at hz; rw [abs_of_nonneg (by omega)]; omega)]
    rw [abs_of_nonneg (by rw [abs_le] at hz; omega)]
    congr 1 <;> omega
  have hpulse (z : ℤ) (hz : |z| ≤ 3) :
      pulse z.natAbs ((z.natAbs+1)/2+2 : ℕ)
        (f n 2 ((z : ZMod n)-((2*A+B : ℤ) : ZMod n))+1) ≤
      pulse z.natAbs ((z.natAbs+1)/2+2 : ℕ) (1+A+(B-z+1)/2) +
      pulse z.natAbs ((z.natAbs+1)/2+2 : ℕ) (1+Ap+(Bp+z+1)/2) := by
    have ha : (z.natAbs : ℤ) ≤ ((z.natAbs+1)/2+2 : ℕ) := by
      have := Int.natCast_natAbs z
      omega
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [hbranch z hz]
    have he : min (A+(B-z+1)/2) (Ap+(Bp+z+1)/2)+1 =
        min (1+A+(B-z+1)/2) (1+Ap+(Bp+z+1)/2) := by omega
    rw [he]
    exact pulse_min_bound _ _ _ _ ha
  rw [outer_two_strip hn]
  have hset : Finset.Icc (-3 : ℤ) 3 = {-3,-2,-1,0,1,2,3} := by decide
  have hz : pulse (0 : ℤ) (2 : ℤ)
      (f n 2 ((0 : ZMod n)-((2*A+B : ℤ) : ZMod n))+1) = 0 := by
    rw [zero_sub, f_neg (by decide : 2 ≤ 2) (by omega : 2*(2+2) ≤ n)]
    unfold pulse sign; split_ifs <;> omega
  have h1 := hpulse 1 (by norm_num)
  have h2 := hpulse 2 (by norm_num)
  have h3 := hpulse 3 (by norm_num)
  have hm1 := hpulse (-1) (by norm_num)
  have hm2 := hpulse (-2) (by norm_num)
  have hm3 := hpulse (-3) (by norm_num)
  rw [hset]
  norm_num only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_zero,
    Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.reduceAdd, Nat.reduceDiv, not_false_eq_true, ne_eq, reduceCtorEq, or_self] at *
  rw [hz]
  unfold PetersenTables.U2 PetersenTables.k2term PetersenTables.g2
  simp only [PetersenTables.pulse_eq, neg_one_mul, one_mul]
  norm_num only [Nat.reduceAdd, Nat.reduceDiv, Nat.cast_ofNat] at *
  simp only [sub_neg_eq_add, ← sub_eq_add_neg] at *
  linarith

end Petersen
```

### `PetersenK2Middle.lean`

```lean
import PetersenK2Outer
import PetersenLowInnerExtended
import PetersenRadii

namespace Petersen
variable {n : ℕ} [NeZero n]

theorem k2_low_witness (hn : 13 ≤ n) (a : ℕ) (ha : 2 ≤ a) (haq : a ≤ (n/2)/2) :
    f n 2 ((2*a : ℕ) : ZMod n) = a ∧ imbalance n 2 ((2*a : ℕ) : ZMod n) < 0 := by
  have hm : 2*(2+2) ≤ n := by omega
  have hi := low_inner_extended (k := 2) (by decide) hm a ha haq
  have hf : f n 2 ((2*a : ℕ) : ZMod n) = a := by simpa [mul_comm] using hi.1
  have hqi : (6 : ℤ) ≤ (n/2 : ℕ) := by omega
  have hr : ((n%2 : ℕ) : ℤ) = 0 ∨ ((n%2 : ℕ) : ℤ) = 1 := by omega
  have hd : (n : ℤ) = 2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  have hc : (((2*(a : ℤ)+0 : ℤ) : ZMod n)) = ((2*a : ℕ) : ZMod n) := by push_cast; ring
  have ho := outer_two_U hn a 0 ((n/2 : ℕ)-a) (n%2 : ℕ)
    (by omega) (by omega) (by omega) (by rw [hc, hf]; exact ha)
  rw [hc] at ho
  have hu := PetersenTables.u2_low_bound (n/2 : ℕ) (n%2 : ℕ) a hqi hr
    (by exact_mod_cast ha) (by omega) (by omega)
  have hii : 4 ≤ innerCount n 2 ((2*a : ℕ) : ZMod n) := by simpa [mul_comm] using hi.2
  refine ⟨hf, ?_⟩
  rw [cancellation (by decide) hm]
  omega

theorem k2_high_witness (hn : 13 ≤ n) (a : ℕ) (ha : (n/2)/2 < a)
    (hex : ∃ j : ZMod n, f n 2 j = a) :
    ∃ j : ZMod n, f n 2 j = a ∧ imbalance n 2 j < 0 := by
  obtain ⟨j,hj⟩ := hex
  have hp : p n j ≤ n/2 := by unfold p; have := j.val_lt; omega
  have hb : a ≤ (n/2+1)/2 := by rw [← hj, f_two_near]; omega
  have hqodd : n/2%2 = 1 := by omega
  have hQ : 3 ≤ (n/2)/2 := by omega
  have hqn : (7 : ℤ) ≤ (n/2 : ℕ) := by omega
  let Q : ℤ := ((n/2)/2 : ℕ)
  let x : ℤ := 2*Q+1
  have hQeq : (n/2 : ℕ) = (2*Q+1 : ℤ) := by dsimp [Q]; omega
  have hd : (n : ℤ) = 2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  have hr : ((n%2 : ℕ) : ℤ) = 0 ∨ ((n%2 : ℕ) : ℤ) = 1 := by omega
  have hx : 0 < x := by dsimp [x, Q]; omega
  have hxn : x < n := by dsimp [x]; omega
  have hc : g 2 x = Q+1 := by unfold g; dsimp [x]; omega
  have hcp : g 2 ((n : ℤ)-x) = Q+1 := by unfold g; dsimp [x]; omega
  have hf : f n 2 (x : ZMod n) = a := by
    have h := f_int_lift (k := 2) (by decide) x (by omega) hxn
    norm_num only [Nat.cast_ofNat] at h
    rw [hc, hcp, min_self] at h
    dsimp [Q] at h
    omega
  have hi := innerCount_four_lifts (k := 2) (by decide) (by omega : 2*(2+2) ≤ n)
    x (Q+1) (Q+1) hx hxn hc hcp (by dsimp [Q]; omega) (by dsimp [Q]; omega)
    (by dsimp [Q]; unfold H; omega) (by dsimp [Q]; unfold H; omega)
    (by dsimp [x, Q]; omega) (by dsimp [x, Q]; omega) (by dsimp [Q]; omega)
  have ho := outer_two_U hn Q 1 (Q+1) ((n%2 : ℕ)-1)
    (by dsimp [Q]; omega) (by dsimp [Q]; omega) (by omega) (by change 2 ≤ f n 2 (x : ZMod n); rw [hf]; omega)
  have hu := PetersenTables.u2_high_bound Q (n%2 : ℕ) (by dsimp [Q]; omega) hr
  refine ⟨(x : ZMod n),hf,?_⟩
  change outerCount n 2 (x : ZMod n) ≤ _ at ho
  rw [cancellation (by decide) (by omega : 2*(2+2) ≤ n)]
  omega

end Petersen
```

### `PetersenFiniteMetric.lean`

```lean
import PetersenSymmetry
import Mathlib.Tactic.FinCases

namespace Petersen

/-- A computable profile is the literal graph distance if its zero, edge and
 predecessor certificates hold. The proof uses ordinary graph walks and kernel reduction. -/
theorem certified_distance {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (d : V → V → ℕ)
    (hz : ∀ x y, d x y = 0 ↔ x = y)
    (he : ∀ x y z, G.Adj x z → d x y ≤ d z y+1)
    (hp : ∀ x y, x ≠ y → ∃ z, G.Adj x z ∧ d x y = d z y+1) :
    ∀ x y, G.dist x y = d x y := by
  have upper : ∀ m x y, d x y = m → G.dist x y ≤ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x y hm
      by_cases hxy : x = y
      · subst y; simp
      · obtain ⟨z,hxz,hd⟩ := hp x y hxy
        have hu := ih (d z y) (by omega) z y rfl
        have ht := hc.dist_triangle (u := x) (v := z) (w := y)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hxz] at ht
        omega
  have lower {x y : V} (w : G.Walk x y) : d x y ≤ w.length := by
    induction w with
    | @nil a => exact Nat.le_of_eq ((hz a a).mpr rfl)
    | @cons a b c hab w ih =>
      have hh := he a c b hab
      simp only [SimpleGraph.Walk.length_cons]
      omega
  intro x y
  apply Nat.le_antisymm (upper (d x y) x y rfl)
  obtain ⟨w,hw⟩ := hc.exists_walk_length_eq_dist x y
  rw [← hw]
  exact lower w

end Petersen
```

### `PetersenFinite11Defs.lean`

```lean
import PetersenFiniteMetric

namespace Petersen

def finiteD11 (x y : Bool × ZMod 11) : ℕ :=
  let z := (y.2-x.2).val
  if x.1 = false ∧ y.1 = false then ([0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1] : List ℕ)[z]!
  else if x.1 = true ∧ y.1 = true then ([0, 3, 1, 4, 2, 3, 3, 2, 4, 1, 3] : List ℕ)[z]!
  else ([1, 2, 2, 3, 3, 4, 4, 3, 3, 2, 2] : List ℕ)[z]!

end Petersen
```

### `PetersenFinite11False.lean`

```lean
import PetersenFinite11Defs

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

theorem row11_false_0 :
  (∀ y, finiteD11 (false,(0 : ZMod 11)) y = 0 ↔ (false,(0 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(0 : ZMod 11)) z → finiteD11 (false,(0 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(0 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(0 : ZMod 11)) z ∧ finiteD11 (false,(0 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_1 :
  (∀ y, finiteD11 (false,(1 : ZMod 11)) y = 0 ↔ (false,(1 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(1 : ZMod 11)) z → finiteD11 (false,(1 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(1 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(1 : ZMod 11)) z ∧ finiteD11 (false,(1 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_2 :
  (∀ y, finiteD11 (false,(2 : ZMod 11)) y = 0 ↔ (false,(2 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(2 : ZMod 11)) z → finiteD11 (false,(2 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(2 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(2 : ZMod 11)) z ∧ finiteD11 (false,(2 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_3 :
  (∀ y, finiteD11 (false,(3 : ZMod 11)) y = 0 ↔ (false,(3 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(3 : ZMod 11)) z → finiteD11 (false,(3 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(3 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(3 : ZMod 11)) z ∧ finiteD11 (false,(3 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_4 :
  (∀ y, finiteD11 (false,(4 : ZMod 11)) y = 0 ↔ (false,(4 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(4 : ZMod 11)) z → finiteD11 (false,(4 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(4 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(4 : ZMod 11)) z ∧ finiteD11 (false,(4 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_5 :
  (∀ y, finiteD11 (false,(5 : ZMod 11)) y = 0 ↔ (false,(5 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(5 : ZMod 11)) z → finiteD11 (false,(5 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(5 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(5 : ZMod 11)) z ∧ finiteD11 (false,(5 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_6 :
  (∀ y, finiteD11 (false,(6 : ZMod 11)) y = 0 ↔ (false,(6 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(6 : ZMod 11)) z → finiteD11 (false,(6 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(6 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(6 : ZMod 11)) z ∧ finiteD11 (false,(6 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_7 :
  (∀ y, finiteD11 (false,(7 : ZMod 11)) y = 0 ↔ (false,(7 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(7 : ZMod 11)) z → finiteD11 (false,(7 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(7 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(7 : ZMod 11)) z ∧ finiteD11 (false,(7 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_8 :
  (∀ y, finiteD11 (false,(8 : ZMod 11)) y = 0 ↔ (false,(8 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(8 : ZMod 11)) z → finiteD11 (false,(8 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(8 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(8 : ZMod 11)) z ∧ finiteD11 (false,(8 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_9 :
  (∀ y, finiteD11 (false,(9 : ZMod 11)) y = 0 ↔ (false,(9 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(9 : ZMod 11)) z → finiteD11 (false,(9 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(9 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(9 : ZMod 11)) z ∧ finiteD11 (false,(9 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_false_10 :
  (∀ y, finiteD11 (false,(10 : ZMod 11)) y = 0 ↔ (false,(10 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (false,(10 : ZMod 11)) z → finiteD11 (false,(10 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (false,(10 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (false,(10 : ZMod 11)) z ∧ finiteD11 (false,(10 : ZMod 11)) y = finiteD11 z y+1) := by decide

end Petersen
```

### `PetersenFinite11True.lean`

```lean
import PetersenFinite11Defs

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

theorem row11_true_0 :
  (∀ y, finiteD11 (true,(0 : ZMod 11)) y = 0 ↔ (true,(0 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(0 : ZMod 11)) z → finiteD11 (true,(0 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(0 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(0 : ZMod 11)) z ∧ finiteD11 (true,(0 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_1 :
  (∀ y, finiteD11 (true,(1 : ZMod 11)) y = 0 ↔ (true,(1 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(1 : ZMod 11)) z → finiteD11 (true,(1 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(1 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(1 : ZMod 11)) z ∧ finiteD11 (true,(1 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_2 :
  (∀ y, finiteD11 (true,(2 : ZMod 11)) y = 0 ↔ (true,(2 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(2 : ZMod 11)) z → finiteD11 (true,(2 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(2 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(2 : ZMod 11)) z ∧ finiteD11 (true,(2 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_3 :
  (∀ y, finiteD11 (true,(3 : ZMod 11)) y = 0 ↔ (true,(3 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(3 : ZMod 11)) z → finiteD11 (true,(3 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(3 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(3 : ZMod 11)) z ∧ finiteD11 (true,(3 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_4 :
  (∀ y, finiteD11 (true,(4 : ZMod 11)) y = 0 ↔ (true,(4 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(4 : ZMod 11)) z → finiteD11 (true,(4 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(4 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(4 : ZMod 11)) z ∧ finiteD11 (true,(4 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_5 :
  (∀ y, finiteD11 (true,(5 : ZMod 11)) y = 0 ↔ (true,(5 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(5 : ZMod 11)) z → finiteD11 (true,(5 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(5 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(5 : ZMod 11)) z ∧ finiteD11 (true,(5 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_6 :
  (∀ y, finiteD11 (true,(6 : ZMod 11)) y = 0 ↔ (true,(6 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(6 : ZMod 11)) z → finiteD11 (true,(6 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(6 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(6 : ZMod 11)) z ∧ finiteD11 (true,(6 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_7 :
  (∀ y, finiteD11 (true,(7 : ZMod 11)) y = 0 ↔ (true,(7 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(7 : ZMod 11)) z → finiteD11 (true,(7 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(7 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(7 : ZMod 11)) z ∧ finiteD11 (true,(7 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_8 :
  (∀ y, finiteD11 (true,(8 : ZMod 11)) y = 0 ↔ (true,(8 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(8 : ZMod 11)) z → finiteD11 (true,(8 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(8 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(8 : ZMod 11)) z ∧ finiteD11 (true,(8 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_9 :
  (∀ y, finiteD11 (true,(9 : ZMod 11)) y = 0 ↔ (true,(9 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(9 : ZMod 11)) z → finiteD11 (true,(9 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(9 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(9 : ZMod 11)) z ∧ finiteD11 (true,(9 : ZMod 11)) y = finiteD11 z y+1) := by decide

theorem row11_true_10 :
  (∀ y, finiteD11 (true,(10 : ZMod 11)) y = 0 ↔ (true,(10 : ZMod 11)) = y) ∧
  (∀ y z, (GP 11 2).Adj (true,(10 : ZMod 11)) z → finiteD11 (true,(10 : ZMod 11)) y ≤ finiteD11 z y+1) ∧
  (∀ y, (true,(10 : ZMod 11)) ≠ y → ∃ z, (GP 11 2).Adj (true,(10 : ZMod 11)) z ∧ finiteD11 (true,(10 : ZMod 11)) y = finiteD11 z y+1) := by decide

end Petersen
```

### `PetersenFinite11Distance.lean`

```lean
import PetersenFinite11False
import PetersenFinite11True

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

theorem finite_rows11 (x : Bool × ZMod 11) :
  (∀ y, finiteD11 x y = 0 ↔ x = y) ∧
  (∀ y z, (GP 11 2).Adj x z → finiteD11 x y ≤ finiteD11 z y+1) ∧
  (∀ y, x ≠ y → ∃ z, (GP 11 2).Adj x z ∧ finiteD11 x y = finiteD11 z y+1) := by
  rcases x with ⟨b,i⟩
  cases b <;> fin_cases i
  all_goals first
    | exact row11_false_0
    | exact row11_false_1
    | exact row11_false_2
    | exact row11_false_3
    | exact row11_false_4
    | exact row11_false_5
    | exact row11_false_6
    | exact row11_false_7
    | exact row11_false_8
    | exact row11_false_9
    | exact row11_false_10
    | exact row11_true_0
    | exact row11_true_1
    | exact row11_true_2
    | exact row11_true_3
    | exact row11_true_4
    | exact row11_true_5
    | exact row11_true_6
    | exact row11_true_7
    | exact row11_true_8
    | exact row11_true_9
    | exact row11_true_10

theorem finite_distance11 : ∀ x y, (GP 11 2).dist x y = finiteD11 x y :=
  certified_distance (gp_connected 11 2) finiteD11
    (fun x => (finite_rows11 x).1) (fun x => (finite_rows11 x).2.1)
    (fun x => (finite_rows11 x).2.2)

end Petersen
```

### `PetersenFinite12Defs.lean`

```lean
import PetersenFiniteMetric

namespace Petersen

def finiteD12 (x y : Bool × ZMod 12) : ℕ :=
  let z := (y.2-x.2).val
  if x.1 = false ∧ y.1 = false then ([0, 1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1] : List ℕ)[z]!
  else if x.1 = true ∧ y.1 = true then ([0, 3, 1, 4, 2, 5, 3, 5, 2, 4, 1, 3] : List ℕ)[z]!
  else ([1, 2, 2, 3, 3, 4, 4, 4, 3, 3, 2, 2] : List ℕ)[z]!

end Petersen
```

### `PetersenFinite12False.lean`

```lean
import PetersenFinite12Defs

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

theorem row12_false_0 :
  (∀ y, finiteD12 (false,(0 : ZMod 12)) y = 0 ↔ (false,(0 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(0 : ZMod 12)) z → finiteD12 (false,(0 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(0 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(0 : ZMod 12)) z ∧ finiteD12 (false,(0 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_1 :
  (∀ y, finiteD12 (false,(1 : ZMod 12)) y = 0 ↔ (false,(1 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(1 : ZMod 12)) z → finiteD12 (false,(1 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(1 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(1 : ZMod 12)) z ∧ finiteD12 (false,(1 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_2 :
  (∀ y, finiteD12 (false,(2 : ZMod 12)) y = 0 ↔ (false,(2 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(2 : ZMod 12)) z → finiteD12 (false,(2 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(2 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(2 : ZMod 12)) z ∧ finiteD12 (false,(2 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_3 :
  (∀ y, finiteD12 (false,(3 : ZMod 12)) y = 0 ↔ (false,(3 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(3 : ZMod 12)) z → finiteD12 (false,(3 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(3 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(3 : ZMod 12)) z ∧ finiteD12 (false,(3 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_4 :
  (∀ y, finiteD12 (false,(4 : ZMod 12)) y = 0 ↔ (false,(4 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(4 : ZMod 12)) z → finiteD12 (false,(4 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(4 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(4 : ZMod 12)) z ∧ finiteD12 (false,(4 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_5 :
  (∀ y, finiteD12 (false,(5 : ZMod 12)) y = 0 ↔ (false,(5 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(5 : ZMod 12)) z → finiteD12 (false,(5 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(5 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(5 : ZMod 12)) z ∧ finiteD12 (false,(5 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_6 :
  (∀ y, finiteD12 (false,(6 : ZMod 12)) y = 0 ↔ (false,(6 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(6 : ZMod 12)) z → finiteD12 (false,(6 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(6 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(6 : ZMod 12)) z ∧ finiteD12 (false,(6 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_7 :
  (∀ y, finiteD12 (false,(7 : ZMod 12)) y = 0 ↔ (false,(7 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(7 : ZMod 12)) z → finiteD12 (false,(7 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(7 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(7 : ZMod 12)) z ∧ finiteD12 (false,(7 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_8 :
  (∀ y, finiteD12 (false,(8 : ZMod 12)) y = 0 ↔ (false,(8 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(8 : ZMod 12)) z → finiteD12 (false,(8 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(8 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(8 : ZMod 12)) z ∧ finiteD12 (false,(8 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_9 :
  (∀ y, finiteD12 (false,(9 : ZMod 12)) y = 0 ↔ (false,(9 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(9 : ZMod 12)) z → finiteD12 (false,(9 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(9 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(9 : ZMod 12)) z ∧ finiteD12 (false,(9 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_10 :
  (∀ y, finiteD12 (false,(10 : ZMod 12)) y = 0 ↔ (false,(10 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(10 : ZMod 12)) z → finiteD12 (false,(10 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(10 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(10 : ZMod 12)) z ∧ finiteD12 (false,(10 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_false_11 :
  (∀ y, finiteD12 (false,(11 : ZMod 12)) y = 0 ↔ (false,(11 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (false,(11 : ZMod 12)) z → finiteD12 (false,(11 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (false,(11 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (false,(11 : ZMod 12)) z ∧ finiteD12 (false,(11 : ZMod 12)) y = finiteD12 z y+1) := by decide

end Petersen
```

### `PetersenFinite12True.lean`

```lean
import PetersenFinite12Defs

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

theorem row12_true_0 :
  (∀ y, finiteD12 (true,(0 : ZMod 12)) y = 0 ↔ (true,(0 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(0 : ZMod 12)) z → finiteD12 (true,(0 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(0 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(0 : ZMod 12)) z ∧ finiteD12 (true,(0 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_1 :
  (∀ y, finiteD12 (true,(1 : ZMod 12)) y = 0 ↔ (true,(1 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(1 : ZMod 12)) z → finiteD12 (true,(1 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(1 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(1 : ZMod 12)) z ∧ finiteD12 (true,(1 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_2 :
  (∀ y, finiteD12 (true,(2 : ZMod 12)) y = 0 ↔ (true,(2 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(2 : ZMod 12)) z → finiteD12 (true,(2 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(2 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(2 : ZMod 12)) z ∧ finiteD12 (true,(2 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_3 :
  (∀ y, finiteD12 (true,(3 : ZMod 12)) y = 0 ↔ (true,(3 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(3 : ZMod 12)) z → finiteD12 (true,(3 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(3 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(3 : ZMod 12)) z ∧ finiteD12 (true,(3 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_4 :
  (∀ y, finiteD12 (true,(4 : ZMod 12)) y = 0 ↔ (true,(4 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(4 : ZMod 12)) z → finiteD12 (true,(4 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(4 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(4 : ZMod 12)) z ∧ finiteD12 (true,(4 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_5 :
  (∀ y, finiteD12 (true,(5 : ZMod 12)) y = 0 ↔ (true,(5 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(5 : ZMod 12)) z → finiteD12 (true,(5 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(5 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(5 : ZMod 12)) z ∧ finiteD12 (true,(5 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_6 :
  (∀ y, finiteD12 (true,(6 : ZMod 12)) y = 0 ↔ (true,(6 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(6 : ZMod 12)) z → finiteD12 (true,(6 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(6 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(6 : ZMod 12)) z ∧ finiteD12 (true,(6 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_7 :
  (∀ y, finiteD12 (true,(7 : ZMod 12)) y = 0 ↔ (true,(7 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(7 : ZMod 12)) z → finiteD12 (true,(7 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(7 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(7 : ZMod 12)) z ∧ finiteD12 (true,(7 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_8 :
  (∀ y, finiteD12 (true,(8 : ZMod 12)) y = 0 ↔ (true,(8 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(8 : ZMod 12)) z → finiteD12 (true,(8 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(8 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(8 : ZMod 12)) z ∧ finiteD12 (true,(8 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_9 :
  (∀ y, finiteD12 (true,(9 : ZMod 12)) y = 0 ↔ (true,(9 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(9 : ZMod 12)) z → finiteD12 (true,(9 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(9 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(9 : ZMod 12)) z ∧ finiteD12 (true,(9 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_10 :
  (∀ y, finiteD12 (true,(10 : ZMod 12)) y = 0 ↔ (true,(10 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(10 : ZMod 12)) z → finiteD12 (true,(10 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(10 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(10 : ZMod 12)) z ∧ finiteD12 (true,(10 : ZMod 12)) y = finiteD12 z y+1) := by decide

theorem row12_true_11 :
  (∀ y, finiteD12 (true,(11 : ZMod 12)) y = 0 ↔ (true,(11 : ZMod 12)) = y) ∧
  (∀ y z, (GP 12 2).Adj (true,(11 : ZMod 12)) z → finiteD12 (true,(11 : ZMod 12)) y ≤ finiteD12 z y+1) ∧
  (∀ y, (true,(11 : ZMod 12)) ≠ y → ∃ z, (GP 12 2).Adj (true,(11 : ZMod 12)) z ∧ finiteD12 (true,(11 : ZMod 12)) y = finiteD12 z y+1) := by decide

end Petersen
```

### `PetersenFinite12Distance.lean`

```lean
import PetersenFinite12False
import PetersenFinite12True

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

theorem finite_rows12 (x : Bool × ZMod 12) :
  (∀ y, finiteD12 x y = 0 ↔ x = y) ∧
  (∀ y z, (GP 12 2).Adj x z → finiteD12 x y ≤ finiteD12 z y+1) ∧
  (∀ y, x ≠ y → ∃ z, (GP 12 2).Adj x z ∧ finiteD12 x y = finiteD12 z y+1) := by
  rcases x with ⟨b,i⟩
  cases b <;> fin_cases i
  all_goals first
    | exact row12_false_0
    | exact row12_false_1
    | exact row12_false_2
    | exact row12_false_3
    | exact row12_false_4
    | exact row12_false_5
    | exact row12_false_6
    | exact row12_false_7
    | exact row12_false_8
    | exact row12_false_9
    | exact row12_false_10
    | exact row12_false_11
    | exact row12_true_0
    | exact row12_true_1
    | exact row12_true_2
    | exact row12_true_3
    | exact row12_true_4
    | exact row12_true_5
    | exact row12_true_6
    | exact row12_true_7
    | exact row12_true_8
    | exact row12_true_9
    | exact row12_true_10
    | exact row12_true_11

theorem finite_distance12 : ∀ x y, (GP 12 2).dist x y = finiteD12 x y :=
  certified_distance (gp_connected 12 2) finiteD12
    (fun x => (finite_rows12 x).1) (fun x => (finite_rows12 x).2.1)
    (fun x => (finite_rows12 x).2.2)

end Petersen
```

### `PetersenFiniteEndpoints.lean`

```lean
import PetersenFinite11Distance
import PetersenFinite12Distance

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Petersen

private theorem finite_diam11 : (GP 11 2).diam = 5 := by
  have hu : ∀ x y, finiteD11 x y ≤ 5 := by decide
  obtain ⟨x,y,he⟩ := (GP 11 2).exists_dist_eq_diam
  have hupper : (GP 11 2).diam ≤ 5 := by rw [← he, finite_distance11]; exact hu x y
  have hlow := (GP 11 2).dist_le_diam ((GP 11 2).connected_iff_ediam_ne_top.mp (gp_connected 11 2))
    (u := (false,0)) (v := (false,5))
  rw [finite_distance11] at hlow
  have hd : finiteD11 (false,0) (false,5) = 5 := by decide
  rw [hd] at hlow
  omega

theorem k2_sharp : 4 < (GP 11 2).diam ∧ LDB (GP 11 2) 4 := by
  constructor
  · rw [finite_diam11]; decide
  · have hb : ∀ x y, finiteD11 x y = 4 →
        (Finset.univ.filter (fun w => finiteD11 x w < finiteD11 y w)).card =
        (Finset.univ.filter (fun w => finiteD11 y w < finiteD11 x w)).card := by decide
    intro x y h
    simp only [finite_distance11] at h
    simpa only [W, finite_distance11] using hb x y h

private theorem finite_diam12 : (GP 12 2).diam = 5 := by
  have hu : ∀ x y, finiteD12 x y ≤ 5 := by decide
  obtain ⟨x,y,he⟩ := (GP 12 2).exists_dist_eq_diam
  have hupper : (GP 12 2).diam ≤ 5 := by rw [← he, finite_distance12]; exact hu x y
  have hlow := (GP 12 2).dist_le_diam ((GP 12 2).connected_iff_ediam_ne_top.mp (gp_connected 12 2))
    (u := (false,0)) (v := (false,5))
  rw [finite_distance12] at hlow
  have hd : finiteD12 (false,0) (false,5) = 5 := by decide
  rw [hd] at hlow
  omega

theorem k2_twelve (ell : ℕ) (h1 : 1 ≤ ell) (hD : ell < (GP 12 2).diam) :
    ¬ LDB (GP 12 2) ell := by
  rw [finite_diam12] at hD
  have hb : ∀ ell : Fin 5, 1 ≤ ell.val → ∃ x y : Bool × ZMod 12,
      finiteD12 x y = ell.val ∧
        (Finset.univ.filter (fun w => finiteD12 x w < finiteD12 y w)).card ≠
        (Finset.univ.filter (fun w => finiteD12 y w < finiteD12 x w)).card := by decide
  obtain ⟨x,y,hd,hn⟩ := hb ⟨ell,hD⟩ h1
  intro h
  apply hn
  have he := h x y (by simpa only [finite_distance12] using hd)
  simpa only [W,finite_distance12] using he

#print axioms k2_sharp
#print axioms k2_twelve
end Petersen
```

### `PetersenK2Boundary.lean`

```lean
import PetersenK2Metric
import PetersenBoundaryOneInner

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n : ℕ} [NeZero n]

private theorem f_two_small (hn : 13 ≤ n) (z : ℤ) (hz : |z| ≤ 5) :
    f n 2 (z : ZMod n) = (z.natAbs+1)/2 := by
  have h := f_two_lift (n := n) (by omega) z (by omega)
  have he : min ((|z|+1)/2) (((n : ℤ)-|z|+1)/2) = (|z|+1)/2 := by omega
  rw [he] at h
  have hab := Int.natCast_natAbs z
  omega

theorem outer_two_small (hn : 13 ≤ n) :
    outerCount n 2 0 = 10 ∧ outerCount n 2 (2 : ZMod n) = 6 := by
  have hset : Finset.Icc (-3 : ℤ) 3 = {-3,-2,-1,0,1,2,3} := by decide
  have hsum (j : ℤ) (hj : |j| ≤ 2) : outerCount n 2 (j : ZMod n) =
      ∑ z ∈ Finset.Icc (-3 : ℤ) 3,
        pulse z.natAbs ((z.natAbs+1)/2+2 : ℕ) (((z-j).natAbs+1)/2+1 : ℕ) := by
    rw [outer_two_strip hn]
    apply Finset.sum_congr rfl
    intro z hz
    have hb := Finset.mem_Icc.mp hz
    have he : (z : ZMod n)-(j : ZMod n) = ((z-j : ℤ) : ZMod n) := by push_cast; rfl
    rw [he, f_two_small hn (z-j) (by rw [abs_le] at hj ⊢; omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · have h := hsum 0 (by norm_num)
    norm_num [hset, pulse, sign] at h
    exact h
  · have h := hsum 2 (by norm_num)
    norm_num [hset, pulse, sign] at h
    exact h

theorem inner_two_small (hn : 13 ≤ n) :
    14 ≤ innerCount n 2 0 ∧ 7 ≤ innerCount n 2 (2 : ZMod n) := by
  classical
  let s : Finset ℤ := Finset.Icc (-3) 3
  have hinj : Function.Injective (fun z : ↥s => (2 : ZMod n)*(z.val : ZMod n)) := by
    intro a b h
    apply Subtype.ext
    apply inner_route_injective_short (k := 2) (by decide) _ h
    have ha := Finset.mem_Icc.mp a.property
    have hb := Finset.mem_Icc.mp b.property
    have hab : |a.val-b.val| ≤ 6 := by rw [abs_le]; omega
    norm_num only [Nat.cast_ofNat]
    omega
  have hfull (z : ↥s) : f n 2 ((2 : ZMod n)*(z.val : ZMod n)) = z.val.natAbs := by
    have hb := Finset.mem_Icc.mp z.property
    have hab := Int.natCast_natAbs z.val
    exact f_signed_inner (k := 2) (by decide) (by omega) z.val (by omega) (by unfold H; omega)
  have hc : Fintype.card ↥s = 7 := by decide
  have hne : (2 : ZMod n) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    change ZMod.val ((2 : ℕ) : ZMod n) = ZMod.val 0 at hh
    rw [ZMod.val_natCast_of_lt (by omega : 2 < n)] at hh
    norm_num at hh
  have hw (j : ZMod n) (hj : j = 0 ∨ j = 2) (z : ↥s) :
      (if j = 0 then (2 : ℤ) else 1) ≤ innerPulse n 2 j ((2 : ZMod n)*(z.val : ZMod n)) := by
    have hf := hfull z
    have h := innerPulse_route (k := 2) (by decide) (by omega) j z.val hf
    norm_num only [Nat.cast_ofNat] at h
    rcases hj with rfl | rfl
    · simpa [zero_sub, f_neg (by decide : 2 ≤ 2) (by omega : 2*(2+2) ≤ n), hf, K] using h
    · have he : (2 : ZMod n)-(2 : ZMod n)*(z.val : ZMod n) =
          -((2 : ZMod n)*(z.val : ZMod n)+(-2)) := by ring
      rw [he, f_neg (by decide : 2 ≤ 2) (by omega : 2*(2+2) ≤ n)] at h
      have hb := f_step_bound (k := 2) (by decide) (by omega)
        ((2 : ZMod n)*(z.val : ZMod n)) (-2) (by right; right; right; rfl)
      rw [hf] at hb
      simp only [ite_eq_right hne]
      have hb1 : (f n 2 ((2 : ZMod n)*(z.val : ZMod n)+(-2)) : ℤ) ≤ z.val.natAbs+1 := by exact_mod_cast hb.1
      have hb2 : (z.val.natAbs : ℤ) ≤ (f n 2 ((2 : ZMod n)*(z.val : ZMod n)+(-2)) : ℤ)+1 := by exact_mod_cast hb.2
      unfold K at h
      split_ifs at h <;> omega
  constructor
  · have hs := innerCount_selected (k := 2) (0 : ZMod n) _ hinj
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hw 0 (Or.inl rfl) z)
    simpa [s, hne] using hh.trans hs
  · have hs := innerCount_selected (k := 2) (2 : ZMod n) _ hinj
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hw 2 (Or.inr rfl) z)
    norm_num at hh
    simpa [s, hne] using hh.trans hs

end Petersen
```

### `PetersenK2.lean`

```lean
import PetersenK2Boundary
import PetersenK2Middle
import PetersenFiniteEndpoints

namespace Petersen
variable {n : ℕ} [NeZero n]

theorem k2_main (hn : 11 < n) (ell : ℕ) (h1 : 1 ≤ ell)
    (hD : ell < (GP n 2).diam) : ¬ LDB (GP n 2) ell := by
  by_cases ht : n = 12
  · subst n; exact k2_twelve ell h1 hD
  · have hn13 : 13 ≤ n := by omega
    have hm : 2*(2+2) ≤ n := by omega
    by_cases he : ell = 1
    · subst ell
      have ho := (outer_two_small hn13).1
      have hi := (inner_two_small hn13).1
      have h := strict_imbalance_of_counts (k := 2) (by decide) hm 0 (by omega)
      simpa only [f_zero (by decide) hm, zero_add] using h
    · by_cases he2 : ell = 2
      · subst ell
        have ho := (outer_two_small hn13).2
        have hi := (inner_two_small hn13).2
        have h := strict_imbalance_of_counts (k := 2) (by decide) hm (2 : ZMod n) (by omega)
        have hf : f n 2 (2 : ZMod n) = 1 := by
          have hh := f_inner_full (k := 2) (by decide) hm 1 (by omega) (by omega)
          simpa using hh
        simpa only [hf] using h
      · have h3 : 3 ≤ ell := by omega
        have hex := subdiam_radius (k := 2) (by decide) hm ell h1 hD
        obtain ⟨j,hj,hi⟩ : ∃ j : ZMod n, f n 2 j = ell-1 ∧ imbalance n 2 j < 0 := by
          by_cases hlow : ell-1 ≤ (n/2)/2
          · exact ⟨((2*(ell-1) : ℕ) : ZMod n), k2_low_witness hn13 (ell-1) (by omega) hlow⟩
          · exact k2_high_witness hn13 (ell-1) (by omega) hex
        have h := not_LDB_of_imbalance (k := 2) (by decide) hm j (ne_of_lt hi)
        simpa only [hj, Nat.sub_add_cancel h1] using h

#print axioms k2_main
end Petersen
```

### `PetersenNonbalance.lean`

```lean
import PetersenLarge
import PetersenK2

namespace Petersen

theorem eventual_nonbalance :
    ∀ k (_hk : 2 ≤ k), ∀ n (hn : nk k < n),
      letI : NeZero n := ⟨by omega⟩
      ∀ ell, 1 ≤ ell → ell < (GP n k).diam → ¬ LDB (GP n k) ell := by
  intro k hk n hn
  let : NeZero n := ⟨by omega⟩
  by_cases he : k = 2
  · subst k
    exact k2_main (by simpa only [nk, ite_true] using hn)
  · exact main_large (by omega) hn

#print axioms eventual_nonbalance
#print eventual_nonbalance
end Petersen
```

### `PetersenShortInner.lean`

```lean
import PetersenBalanceCounts
import PetersenPulses

namespace Petersen
variable {n k : ℕ} [NeZero n]

/-- Every strict inner shortcut has a shortest pure inner route. -/
theorem inner_short_route (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n)
    (hi : innerProfile n k i < f n k i+2) :
    ∃ z : ℤ, (k : ZMod n)*(z : ZMod n) = i ∧ z.natAbs = innerProfile n k i := by
  obtain ⟨w,hw⟩ := (gp_connected n k).exists_walk_length_eq_dist (true,0) (true,i)
  have hd : (GP n k).dist (true,0) (true,i) = innerProfile n k i := by
    simpa only [sub_zero] using (profiles hk hn 0 i).2.2
  rw [hd] at hw
  obtain ⟨a,b,s,he,hl,hpar,hpure⟩ := walk_step_counts w
  have he' : (a : ZMod n)+(k : ZMod n)*(b : ZMod n) = i := by simpa using he.symm
  have hf := cyclic_lower hk hn i a b he'
  have hs : s = 0 := by simp only [ite_true] at hpar; omega
  have ha : a = 0 := (hpure hs).2 rfl
  have hb : (k : ZMod n)*(b : ZMod n) = i := by simpa [ha] using he'
  refine ⟨b,hb,?_⟩
  have hu := innerProfile_le_route (n := n) (k := k) b
  rw [hb] at hu
  simp only [ha, Int.natAbs_zero, zero_add] at hl
  omega

/-- A word route gives a lower bound for each same-layer distance. -/
theorem f_le_innerProfile (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (i : ZMod n) :
    f n k i ≤ innerProfile n k i := by
  by_cases hi : innerProfile n k i < f n k i+2
  · obtain ⟨z,hz,hl⟩ := inner_short_route hk hn i hi
    have h := cyclic_lower hk hn i 0 z (by simpa using hz)
    simpa only [Int.natAbs_zero, zero_add, hl] using h
  · omega

end Petersen
```

### `PetersenBalanceTransfer.lean`

```lean
import PetersenShortInner

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem f_eq_zero_iff (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (j : ZMod n) :
    f n k j = 0 ↔ j = 0 := by
  constructor
  · intro h
    obtain ⟨a,b,he,hl⟩ := word_exists (k := k) j
    rw [word_eq_f hk hn, h] at hl
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    simpa [ha,hb] using he.symm
  · rintro rfl; exact f_zero hk hn

theorem mixed_balanced_of_imbalance (i j : ZMod n) (h : imbalance n k (j-i) = 0) :
    (W (GP n k) (false,i) (true,j)).card = (W (GP n k) (true,j) (false,i)).card := by
  let e : GP n k ≃g GP n k := (reflectionIso i).trans (reflectionIso 0)
  have hf := iso_W_card (gp_connected n k) e (false,i) (true,j)
  have hr := iso_W_card (gp_connected n k) e (true,j) (false,i)
  have hf' : (W (GP n k) (false,0) (true,j-i)).card = (W (GP n k) (false,i) (true,j)).card := by
    simpa [e,reflectionIso,reflection] using hf
  have hr' : (W (GP n k) (true,j-i) (false,0)).card = (W (GP n k) (true,j) (false,i)).card := by
    simpa [e,reflectionIso,reflection] using hr
  unfold imbalance at h
  omega

/-- Every mixed pair in the selected distance class, together with reflections
within the two layers, proves the whole LDB class. -/
theorem LDB_of_mixed (hk : 2 ≤ k) (hn : k*(k+2) ≤ n) (ell : ℕ)
    (h : ∀ j : ZMod n, f n k j+1 = ell → imbalance n k j = 0) :
    LDB (GP n k) ell := by
  rintro ⟨a,i⟩ ⟨b,j⟩ hd
  cases a <;> cases b
  · exact same_layer_balanced false i j
  · apply mixed_balanced_of_imbalance
    apply h
    simpa only [(profiles hk hn i j).1] using hd
  · symm
    apply mixed_balanced_of_imbalance
    apply h
    rw [SimpleGraph.dist_comm] at hd
    simpa only [(profiles hk hn j i).1] using hd
  · exact same_layer_balanced true i j

end Petersen
```

### `PetersenInnerZeroExact.lean`

```lean
import PetersenShortInner
import PetersenRayInjection
import Mathlib.Tactic.LinearCombination

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n k q : ℕ} [NeZero n]

/-- At n=kq the inner shortcut vertices form one q-cycle, counted once. -/
theorem inner_zero_multiple (hk : 2 ≤ k) (hn : k*(k+2) ≤ n)
    (hq : 0 < q) (heq : n = k*q) : innerCount n k 0 = 2*(q : ℤ) := by
  classical
  let idx : Fin q → ZMod n := fun a => ((k*a.val : ℕ) : ZMod n)
  have hinj : Function.Injective idx := by
    intro a b h
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    have hz : (a.val : ℤ) = b.val := inner_route_injective_short (n := n) (k := k) (by omega)
      (by
        have hab : |(a.val : ℤ)-b.val| < q := by rw [abs_lt]; omega
        have hw := mul_lt_mul_of_pos_left hab (show (0 : ℤ) < k by omega)
        have hn' : (n : ℤ) = (k : ℤ)*q := by exact_mod_cast heq
        omega)
      (by simpa only [idx, Nat.cast_mul, Int.cast_natCast] using h)
    omega
  have route_image (z : ℤ) : ∃ a : Fin q, idx a = (k : ZMod n)*(z : ZMod n) := by
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    let r : ℕ := (z%(q : ℤ)).toNat
    have hr : (r : ℤ) = z%(q : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    have hrq : r < q := by have := Int.emod_lt_of_pos z hqz; omega
    refine ⟨⟨r,hrq⟩,?_⟩
    have hz := Int.emod_add_mul_ediv z (q : ℤ)
    have hn' : (n : ℤ) = (k : ℤ)*q := by exact_mod_cast heq
    have hdiff : (k : ℤ)*z-(k : ℤ)*r = (n : ℤ)*(z/(q : ℤ)) := by
      rw [hr, hn']
      linear_combination -(k : ℤ)*hz
    have hcast := congrArg (fun t : ℤ => (t : ZMod n)) hdiff
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul] at hcast
    dsimp [idx]
    push_cast
    linear_combination -hcast
  have hval (a : Fin q) : innerPulse n k 0 (idx a) = 2 := by
    have ha := a.isLt
    have hdiv : n/k = q := by rw [heq]; simp [Nat.ne_of_gt (show 0 < k by omega)]
    have hmod : n%k = 0 := by rw [heq]; simp
    have hf : f n k (idx a) = min a.val (q-a.val) := by
      dsimp [idx]
      rw [f_inner_multiple hk hn a.val (by omega), hdiv, hmod]
      simp [H]
    have hp : innerProfile n k (idx a) ≤ min a.val (q-a.val) := by
      apply le_min
      · have hh := innerProfile_le_route (n := n) (k := k) (a.val : ℤ)
        simpa only [Int.cast_natCast, Int.natAbs_natCast, idx, Nat.cast_mul] using hh
      · have hz : (k : ZMod n)*(-((q-a.val : ℕ) : ℤ) : ZMod n) = idx a := by
          have hcast : (k : ZMod n)*(q : ZMod n) = 0 := by rw [← Nat.cast_mul, ← heq]; exact ZMod.natCast_self n
          dsimp [idx]
          simp only [Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
          rw [Nat.cast_sub (by omega : a.val ≤ q)]
          linear_combination -hcast
        have hh := innerProfile_le_route (n := n) (k := k) (-((q-a.val : ℕ) : ℤ))
        simp only [Int.cast_neg, Int.cast_natCast] at hz hh
        rw [hz] at hh
        simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hh
    have hprof : innerProfile n k (idx a) = f n k (idx a) := by
      have hh := f_le_innerProfile hk hn (idx a)
      omega
    simp [innerPulse, sub_zero, hprof, pulse, sign]
  have hv (i : ZMod n) (hi : i ∉ Finset.univ.image idx) : innerPulse n k 0 i = 0 := by
    have he : innerProfile n k i = f n k i+2 := by
      by_contra h
      have hb := innerProfile_le (k := k) i
      obtain ⟨z,hz,_⟩ := inner_short_route hk hn i (by omega)
      obtain ⟨a,ha⟩ := route_image z
      exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.trans hz⟩)
    simp [innerPulse, he, pulse]
  rw [innerCount_sum]
  have hsum : (∑ i ∈ Finset.univ.image idx, innerPulse n k 0 i) = ∑ i, innerPulse n k 0 i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact hv i hi
  rw [← hsum, Finset.sum_image (fun a _ b _ h => hinj h)]
  simp [hval, mul_comm]

end Petersen
```

### `PetersenOddMetric.lean`

```lean
import PetersenBalanceTransfer
import PetersenOuterBridge
import PetersenArithmetic
import PetersenInnerArithmetic

namespace Petersen
variable {n k : ℕ} [NeZero n]

def oddX (h k : ℕ) : ℕ := (h+1)*k+(h+1)

private theorem odd_line_upper (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (s : ℕ) (hs : s ≤ oddX h k) : lineCost k s ≤ 2*h+2 := by
  have hd := Nat.div_add_mod s k
  have hr := Nat.mod_lt s (by omega : 0 < k)
  have hH : H k (s%k) ≤ h+1 := by unfold H; omega
  have hq : s/k ≤ h+1 := by
    by_contra hq
    have hm := Nat.mul_le_mul_right k (show h+2 ≤ s/k by omega)
    dsimp [oddX] at hs
    have hsk : (h+2)*k ≤ s := hm.trans (by nlinarith only [hd, Nat.zero_le (s%k)])
    have hex : (h+1)*k+(h+1) < (h+2)*k := by nlinarith only [show h+1 < k by omega]
    omega
  unfold lineCost
  omega

private theorem odd_line_lower (h : ℕ) (_hh : 1 ≤ h) (hk : k = 2*h+1)
    (s : ℕ) (hs : 2*h+2 ≤ lineCost k s) : oddX h k ≤ s := by
  have hd := Nat.div_add_mod s k
  have hr := Nat.mod_lt s (by omega : 0 < k)
  have hH : H k (s%k) ≤ h+1 := by unfold H; omega
  have hq : h+1 ≤ s/k := by unfold lineCost at hs; omega
  by_cases he : s/k = h+1
  · have hb : h+1 ≤ s%k := by unfold lineCost H at hs; omega
    dsimp [oddX]
    nlinarith
  · have hm := Nat.mul_le_mul_right k (show h+2 ≤ s/k by omega)
    dsimp [oddX]
    have hsk : (h+2)*k ≤ s := hm.trans (by nlinarith only [hd, Nat.zero_le (s%k)])
    have hex : (h+1)*k+(h+1) ≤ (h+2)*k := by nlinarith only [show h+1 ≤ k by omega]
    exact hex.trans hsk

theorem odd_f_bound (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) (j : ZMod n) : f n k j ≤ 2*h+2 := by
  have hp : p n j ≤ oddX h k := by unfold p; have := j.val_lt; omega
  have hu := odd_line_upper h hh hk (p n j) hp
  rw [f_near]
  exact (min_le_left _ _).trans hu

theorem odd_f_max_unique (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) (j : ZMod n) (hj : f n k j = 2*h+2) :
    j = ((oddX h k : ℕ) : ZMod n) := by
  have h1 : 2*h+2 ≤ lineCost k j.val := by rw [← hj]; exact min_le_left _ _
  have h2 : 2*h+2 ≤ lineCost k (n-j.val) := by rw [← hj]; exact min_le_right _ _
  have ha := odd_line_lower h hh hk j.val h1
  have hb := odd_line_lower h hh hk (n-j.val) h2
  have hv := j.val_lt
  have he : j.val = oddX h k := by omega
  rw [← he, ZMod.natCast_zmod_val]

theorem odd_f_center (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) : f n k ((oddX h k : ℕ) : ZMod n) = 2*h+2 := by
  have hx : 0 < oddX h k := by dsimp [oddX]; positivity
  have hv : oddX h k < n := by omega
  unfold f
  rw [ZMod.val_natCast_of_lt hv, show n-oddX h k = oddX h k by omega, min_self]
  rw [oddX, lineCost_block (by omega) _ _ (by omega)]
  unfold H
  omega

theorem odd_diameter (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) : (GP n k).diam = 2*h+4 := by
  have hm : k*(k+2) ≤ n := by dsimp [oddX] at hn; nlinarith
  have hF : F n k ≤ 2*h+2 := by
    apply Finset.sup_le
    intro j _
    exact odd_f_bound h hh hk hn j
  have hu := diam_le_F_add_two (by omega : 2 ≤ k) hm
  have hx : 0 < oddX h k := by dsimp [oddX]; positivity
  have hp : p n ((oddX h k : ℕ) : ZMod n) = oddX h k := by
    unfold p
    rw [ZMod.val_natCast_of_lt (by omega : oddX h k < n)]
    omega
  have hdist : (GP n k).dist (false,0) (false,((oddX h k : ℕ) : ZMod n)) = 2*h+4 := by
    rw [(profiles (by omega) hm 0 _).2.1]
    simp only [sub_zero, outerProfile, hp, odd_f_center h hh hk hn]
    apply min_eq_right
    dsimp [oddX]
    nlinarith
  have hd := (GP n k).dist_le_diam ((GP n k).connected_iff_ediam_ne_top.mp (gp_connected n k))
    (u := (false,0)) (v := (false,((oddX h k : ℕ) : ZMod n)))
  omega

end Petersen
```

### `PetersenSharpEven.lean`

```lean
import PetersenInnerZeroExact
import PetersenBoundaryOuter
import PetersenBalanceTransfer
import PetersenArithmetic

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem multiple_balanced_one (hk : 3 ≤ k) (hn : n = k*(k+2)) :
    1 < (GP n k).diam ∧ LDB (GP n k) 1 := by
  have hm : k*(k+2) ≤ n := by omega
  have hi := inner_zero_multiple (n := n) (q := k+2) (by omega : 2 ≤ k) hm (by omega) hn
  have ho := outer_zero hk hm
  have hz : imbalance n k 0 = 0 := by rw [cancellation (by omega) hm]; omega
  constructor
  · have hdist : (GP n k).dist (false,0) (false,2) = 2 := by
      rw [(profiles (by omega) hm 0 2).2.1]
      simp only [sub_zero, outerProfile]
      have hp := p_intCast_strip (n := n) (m := 2) (by nlinarith) 2 (by norm_num)
      norm_num at hp
      rw [hp]
      omega
    have hd := (GP n k).dist_le_diam ((GP n k).connected_iff_ediam_ne_top.mp (gp_connected n k))
      (u := (false,0)) (v := (false,2))
    omega
  · apply LDB_of_mixed (by omega) hm 1
    intro j hj
    have he : j = 0 := (f_eq_zero_iff (by omega) hm j).mp (by omega)
    simpa only [he] using hz

theorem sharp_even (k : ℕ) (hk : 4 ≤ k) (he : Even k) :
    letI : NeZero (nk k) := ⟨Nat.ne_of_gt (nk_pos k (by omega))⟩
    1 < (GP (nk k) k).diam ∧ LDB (GP (nk k) k) 1 := by
  let : NeZero (nk k) := ⟨Nat.ne_of_gt (nk_pos k (by omega))⟩
  have hnk : nk k = k*(k+2) := by rw [nk_eq (by omega), Nat.even_iff.mp he]; omega
  exact multiple_balanced_one (by omega) hnk

#print axioms sharp_even
end Petersen
```

### `PetersenOddCross.lean`

```lean
import PetersenOddMetric
import Mathlib.Tactic.LinearCombination

set_option linter.unusedSimpArgs false
namespace Petersen
variable {n k : ℕ} [NeZero n]

omit [NeZero n] in
theorem odd_antipode (h : ℕ) (hn : n = 2*oddX h k) :
    -((oddX h k : ℕ) : ZMod n) = ((oddX h k : ℕ) : ZMod n) := by
  have hz : (2 : ZMod n)*((oddX h k : ℕ) : ZMod n) = 0 := by
    change ((2 : ℕ) : ZMod n)*((oddX h k : ℕ) : ZMod n) = 0
    rw [← Nat.cast_mul, ← hn]
    exact ZMod.natCast_self n
  linear_combination -hz

theorem odd_center_strip (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) (t : ℤ) (ht : 0 ≤ t) (hth : t ≤ h+1) :
    (f n k ((((oddX h k : ℕ) : ZMod n))-(t : ZMod n)) : ℤ) = 2*h+2-t := by
  have hx : (oddX h k : ℤ) = ((h : ℤ)+1)*k+(h+1) := by simp [oddX]
  have hni : (n : ℤ) = 2*((h+1 : ℕ)*(k : ℤ)+(h+1 : ℕ)) := by exact_mod_cast hn
  have he : ((oddX h k : ℕ) : ZMod n)-(t : ZMod n) =
      (((oddX h k : ℕ) : ℤ)-t : ℤ) := by push_cast; rfl
  rw [he, f_int_lift (by omega) _ (by rw [hx]; nlinarith) (by rw [hx]; nlinarith)]
  have hg (s : ℤ) (hs : 0 ≤ s) (hsk : s ≤ (k : ℤ)+1) :
      g k (((h : ℤ)+1)*k+s) = (h+1 : ℕ)+PetersenTables.localG k s := by
    rw [g_translate _ _ _ (by omega), ← localG_eq_g k s (by omega) (by omega) (by omega)]
    push_cast; rfl
  rw [hx, show ((h : ℤ)+1)*k+(h+1)-t = ((h : ℤ)+1)*k+(h+1-t) by ring,
    show (n : ℤ)-(((h : ℤ)+1)*k+(h+1-t)) = ((h : ℤ)+1)*k+(h+1+t) by
      push_cast at hni; linarith,
    hg _ (by omega) (by omega), hg _ (by omega) (by omega)]
  unfold PetersenTables.localG
  split_ifs <;> omega

private theorem odd_center_inner_pos (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) (t : ℤ) (ht : 0 ≤ t) (hth : t ≤ h+2) :
    (f n k ((((oddX h k : ℕ) : ZMod n))-(k : ZMod n)*(t : ZMod n)) : ℤ) = 2*h+2-t := by
  have hm : k*(k+2) ≤ n := by dsimp [oddX] at hn; nlinarith
  by_cases hb : t ≤ h+1
  · have hx : (oddX h k : ℤ) = ((h : ℤ)+1)*k+(h+1) := by simp [oddX]
    have hni : (n : ℤ) = 2*(((h : ℤ)+1)*k+(h+1)) := by exact_mod_cast hn
    have he : ((oddX h k : ℕ) : ZMod n)-(k : ZMod n)*(t : ZMod n) =
        ((((h : ℤ)+1-t)*k+(h+1) : ℤ) : ZMod n) := by rw [← Int.cast_natCast, hx]; push_cast; ring
    rw [he, f_int_lift (by omega) _ (by nlinarith) (by nlinarith)]
    rw [show (n : ℤ)-(((h : ℤ)+1-t)*k+(h+1)) = ((h : ℤ)+1+t)*k+(h+1) by linarith]
    rw [g_block _ _ _ (by omega) (by omega) (by omega),
      g_block _ _ _ (by omega) (by omega) (by omega)]
    omega
  · have ht' : t = h+2 := by omega
    have he : ((oddX h k : ℕ) : ZMod n)-(k : ZMod n)*(t : ZMod n) = -((h : ℕ) : ZMod n) := by
      dsimp [oddX]
      push_cast
      have htcast : (t : ZMod n) = ((h+2 : ℕ) : ZMod n) := by rw [ht']; push_cast; rfl
      rw [htcast]
      push_cast
      have hkc : (k : ZMod n) = 2*(h : ZMod n)+1 := by
        have hc := congrArg (fun a : ℕ => (a : ZMod n)) hk
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hc
      rw [hkc]; ring
    rw [he, f_neg (by omega) hm]
    have hp := p_intCast_strip (n := n) (m := h) (by dsimp [oddX] at hn; nlinarith) (h : ℤ) (by simp)
    have hp' : p n (h : ZMod n) = h := by simpa using hp
    rw [f_short_near (by omega) hm _ (by rw [hp']; omega), hp']
    unfold H
    omega

theorem odd_center_inner (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) (z : ℤ) (hz : |z| ≤ h+2) :
    (f n k ((((oddX h k : ℕ) : ZMod n))-(k : ZMod n)*(z : ZMod n)) : ℤ) = 2*h+2-|z| := by
  by_cases hp : 0 ≤ z
  · rw [abs_of_nonneg hp]
    exact odd_center_inner_pos h hh hk hn z hp (by rw [abs_of_nonneg hp] at hz; exact hz)
  · have he : ((oddX h k : ℕ) : ZMod n)-(k : ZMod n)*(z : ZMod n) =
        -(((oddX h k : ℕ) : ZMod n)-(k : ZMod n)*((-z : ℤ) : ZMod n)) := by
      rw [neg_sub]
      simp only [sub_eq_add_neg, odd_antipode h hn]
      push_cast; ring
    have hm : k*(k+2) ≤ n := by dsimp [oddX] at hn; nlinarith
    rw [he, f_neg (by omega) hm, odd_center_inner_pos h hh hk hn (-z) (by omega) (by rw [abs_of_neg (by omega)] at hz; exact hz), abs_of_neg (by omega)]

end Petersen
```

### `PetersenOddOuter.lean`

```lean
import PetersenOddCross

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem odd_outer_count (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) : outerCount n k ((oddX h k : ℕ) : ZMod n) = 4 := by
  have hm : k*(k+2) ≤ n := by dsimp [oddX] at hn; nlinarith
  have hdiv : k/2+1 = h+1 := by omega
  let j : ZMod n := ((oddX h k : ℕ) : ZMod n)
  rw [outerCount_strip (by omega) hm, sum_symmetric, hdiv]
  have hz : pulse (0 : ℤ) (H k 0+2) (f n k ((0 : ZMod n)-j)+1) = 0 := by
    rw [zero_sub, f_neg (by omega) hm]
    have hf : f n k j = 2*h+2 := odd_f_center h hh hk hn
    rw [hf]
    unfold H pulse sign
    split_ifs <;> omega
  simp only [Int.natAbs_zero, Int.cast_zero, Nat.cast_zero, hz, zero_add]
  have hsum : (∑ t ∈ Finset.Icc 1 ((h+1 : ℕ) : ℤ),
      (pulse (-t).natAbs (H k (-t).natAbs+2) (f n k (((-t : ℤ) : ZMod n)-j)+1) +
       pulse t.natAbs (H k t.natAbs+2) (f n k ((t : ZMod n)-j)+1))) =
      ∑ t ∈ Finset.Icc 1 ((h+1 : ℕ) : ℤ), (if t = (h+1 : ℕ) then 4 else 0 : ℤ) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hb := Finset.mem_Icc.mp ht
    have hab : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have hH : H k t.natAbs = t.natAbs := by unfold H; omega
    have he : ((-t : ℤ) : ZMod n)-j = j-(t : ZMod n) := by
      dsimp [j]
      simp only [Int.cast_neg, sub_eq_add_neg, odd_antipode h hn]
      ring
    have hf := odd_center_strip h hh hk hn t (by omega) (by omega)
    change (f n k (j-(t : ZMod n)) : ℤ) = _ at hf
    rw [he, ← neg_sub j (t : ZMod n), f_neg (by omega) hm]
    simp only [Int.natAbs_neg, hH, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hab, hf]
    unfold pulse sign
    split_ifs <;> omega
  rw [hsum]
  simp [Finset.sum_ite_eq', Finset.mem_Icc]
  simpa only [j, zero_sub] using hz

end Petersen
```

### `PetersenOddInner.lean`

```lean
import PetersenOddCross
import PetersenInnerLifts

set_option linter.unusedSimpArgs false
namespace Petersen
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

theorem odd_inner_count (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) : innerCount n k ((oddX h k : ℕ) : ZMod n) = 4 := by
  have hm : k*(k+2) ≤ n := by dsimp [oddX] at hn; nlinarith
  have heqn : n = (k+2)*k+1 := by dsimp [oddX] at hn; nlinarith
  have hq : n/k = k+2 := by
    rw [heqn, add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < k), Nat.div_eq_of_lt (by omega : 1 < k), zero_add]
  have hr : n%k = 1 := by rw [heqn]; simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < k)]
  let j : ZMod n := ((oddX h k : ℕ) : ZMod n)
  let root : ZMod n := (k : ZMod n)*((h+1 : ℕ) : ZMod n)
  have hu (i : ZMod n) : innerPulse n k j i ≤
      (if i = root then (2 : ℤ) else 0)+(if i = -root then 2 else 0) := by
    by_cases he : innerProfile n k i = f n k i+2
    · simp only [innerPulse, he, Nat.cast_add, Nat.cast_ofNat, pulse, sub_self]
      split_ifs <;> omega
    · have hi := innerProfile_le (k := k) i
      obtain ⟨z,hz,hl⟩ := inner_short_route (by omega : 2 ≤ k) hm i
        (by have := innerProfile_le (k := k) i; omega)
      have ht : z.natAbs ≤ n/k := by
        have hb := odd_f_bound h hh hk hn i
        rw [hq]
        omega
      have hf : f n k i = min z.natAbs (n/k-z.natAbs+H k (n%k)) := by
        have hv := f_inner_multiple (by omega : 2 ≤ k) hm z.natAbs ht
        have hab : ((z.natAbs : ℕ) : ZMod n) =
            if 0 ≤ z then (z : ZMod n) else -(z : ZMod n) := by
          by_cases hp : 0 ≤ z
          · rw [ite_eq_left hp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hp]
          · rw [ite_eq_right hp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg (by omega), Int.cast_neg]
        by_cases hp : 0 ≤ z
        · simpa only [Nat.cast_mul, hab, ite_eq_left hp, hz] using hv
        · simpa only [Nat.cast_mul, hab, ite_eq_right hp, mul_neg, hz, f_neg (by omega) hm] using hv
      have hsmall : z.natAbs ≤ h+2 := by
        rw [hq,hr] at hf
        unfold H at hf
        have hb := innerProfile_le (k := k) i
        omega
      have hfi : f n k i = z.natAbs := by
        rw [hf, hq, hr]
        unfold H
        omega
      have hcross := odd_center_inner h hh hk hn z (by
        have ha := Int.natCast_natAbs z
        omega)
      have hpulse : innerPulse n k j i = if z.natAbs = h+1 then 2 else 0 := by
        have hcr : (f n k (j-i) : ℤ) = 2*h+2-(z.natAbs : ℤ) := by
          dsimp [j]
          rw [← hz]
          simpa only [Int.natCast_natAbs] using hcross
        unfold innerPulse
        rw [← neg_sub j i, f_neg (by omega) hm, ← hl, hfi]
        rw [hcr]
        unfold pulse sign
        split_ifs <;> omega
      rw [hpulse]
      by_cases ht' : z.natAbs = h+1
      · rw [ite_eq_left ht']
        have hz' : z = ((h+1 : ℕ) : ℤ) ∨ z = -((h+1 : ℕ) : ℤ) := by
          have ha := Int.natCast_natAbs z
          omega
        have hi : i = root ∨ i = -root := by
          rw [← hz]
          dsimp [root]
          rcases hz' with rfl | rfl
          · left; simp only [Int.cast_natCast]
          · right; push_cast; ring
        rcases hi with hi | hi <;> simp [hi] <;> split_ifs <;> omega
      · rw [ite_eq_right ht']; split_ifs <;> omega
  have hupper : innerCount n k j ≤ 4 := by
    rw [innerCount_sum]
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hu i)
    simpa [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq] using hb
  have hx : (oddX h k : ℤ) = ((h : ℤ)+1)*k+(h+1) := by simp [oddX]
  have hc : g k (oddX h k : ℕ) = 2*h+2 := by
    rw [hx, g_block _ _ _ (by omega) (by omega) (by omega)]
    omega
  have hcp : g k ((n : ℤ)-(oddX h k : ℕ)) = 2*h+2 := by
    have he : (n : ℤ)-(oddX h k : ℕ) = (oddX h k : ℕ) := by
      have hi : (n : ℤ) = 2*(oddX h k : ℕ) := by exact_mod_cast hn
      omega
    rw [he]; exact hc
  have hlower := innerCount_four_lifts (by omega : 2 ≤ k) hm (oddX h k : ℕ)
    (2*h+2) (2*h+2) (by rw [hx]; nlinarith) (by dsimp [oddX] at *; nlinarith)
    hc hcp (by omega) (by omega)
    (by rw [hq,hr]; unfold H; omega) (by rw [hq,hr]; unfold H; omega)
    (by rw [hx]; nlinarith [show (2*(h : ℤ)+2+1)/2 = h+1 by omega])
    (by have hi : (n : ℤ) = 2*(oddX h k : ℕ) := by exact_mod_cast hn
        rw [hx] at hi; nlinarith [show (2*(h : ℤ)+2+1)/2 = h+1 by omega])
    (by have hi : (n : ℤ) = 2*(oddX h k : ℕ) := by exact_mod_cast hn
        rw [hx] at hi; nlinarith [show (2*(h : ℤ)+2+1)/2 = h+1 by omega])
  simp only [Int.cast_natCast] at hlower
  change 4 ≤ innerCount n k j at hlower
  change innerCount n k j = 4
  omega

end Petersen
```

### `PetersenSharpOdd.lean`

```lean
import PetersenOddInner
import PetersenOddOuter

namespace Petersen
variable {n k : ℕ} [NeZero n]

theorem odd_balanced_class (h : ℕ) (hh : 1 ≤ h) (hk : k = 2*h+1)
    (hn : n = 2*oddX h k) :
    2*h+3 < (GP n k).diam ∧ LDB (GP n k) (2*h+3) := by
  have hm : k*(k+2) ≤ n := by dsimp [oddX] at hn; nlinarith
  have hz : imbalance n k ((oddX h k : ℕ) : ZMod n) = 0 := by
    rw [cancellation (by omega) hm, odd_outer_count h hh hk hn, odd_inner_count h hh hk hn]
    omega
  constructor
  · rw [odd_diameter h hh hk hn]; omega
  · apply LDB_of_mixed (by omega) hm (2*h+3)
    intro j hj
    have he := odd_f_max_unique h hh hk hn j (by omega)
    simpa only [he] using hz

theorem sharp_odd (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    letI : NeZero (nk k) := ⟨Nat.ne_of_gt (nk_pos k (by omega))⟩
    2*(k/2)+3 < (GP (nk k) k).diam ∧ LDB (GP (nk k) k) (2*(k/2)+3) := by
  let : NeZero (nk k) := ⟨Nat.ne_of_gt (nk_pos k (by omega))⟩
  have hp : k%2 = 1 := Nat.odd_iff.mp ho
  have he : k = 2*(k/2)+1 := by omega
  have hn : nk k = 2*oddX (k/2) k := by
    rw [nk_eq hk, hp]
    dsimp [oddX]
    nlinarith
  exact odd_balanced_class (k/2) (by omega) he hn

#print axioms odd_balanced_class
#print axioms sharp_odd
end Petersen
```

### `PetersenFinal.lean`

```lean
import PetersenNonbalance
import PetersenSharpEven
import PetersenSharpOdd

namespace Petersen

theorem k2_sharp_at (n : ℕ) [NeZero n] (hn : n = 11) :
    ∃ ell, 1 ≤ ell ∧ ell < (GP n 2).diam ∧ LDB (GP n 2) ell := by
  subst n
  exact ⟨4, by decide, k2_sharp.1, k2_sharp.2⟩

/-- The literal three-part endpoint fixed by the adversarial review. -/
theorem miklavic_sparl_4_4 : MiklavicSparl44 := by
  refine ⟨eventual_connected, eventual_nonbalance, ?_⟩
  intro k hk
  let : NeZero (nk k) := ⟨Nat.ne_of_gt (nk_pos k hk)⟩
  by_cases he : k = 2
  · subst k
    exact k2_sharp_at (nk 2) (by norm_num [nk])
  · rcases Nat.even_or_odd k with hp | hp
    · have h := sharp_even k (by have := Nat.even_iff.mp hp; omega) hp
      exact ⟨1, by decide, h.1, h.2⟩
    · have h := sharp_odd k (by omega) hp
      exact ⟨2*(k/2)+3, by omega, h.1, h.2⟩

#print axioms miklavic_sparl_4_4
#print miklavic_sparl_4_4
#check (miklavic_sparl_4_4 : MiklavicSparl44)
end Petersen
```

### `PetersenStageFourAudit.lean`

```lean
import PetersenFinal

#print axioms Petersen.outer_zero
#print axioms Petersen.inner_route_injective
#print axioms Petersen.inner_route_injective_short
#print axioms Petersen.f_signed_inner
#print axioms Petersen.inner_zero_interval
#print axioms Petersen.inner_zero_lower
#print axioms Petersen.outer_one
#print axioms Petersen.inner_one_interval
#print axioms Petersen.inner_one_lower
#print axioms Petersen.witness_zero
#print axioms Petersen.witness_one
#print axioms Petersen.main_large
#print axioms Petersen.large_eventual_nonbalance
#print axioms Petersen.low_inner_extended
#print axioms Petersen.lineCost_two
#print axioms Petersen.f_two_near
#print axioms Petersen.f_two_lift
#print axioms Petersen.outer_two_strip
#print axioms PetersenTables.u2_zero
#print axioms PetersenTables.u2_one
#print axioms PetersenTables.u2_negative
#print axioms PetersenTables.u2_low_bound
#print axioms PetersenTables.u2_high_bound
#print axioms Petersen.outer_two_U
#print axioms Petersen.k2_low_witness
#print axioms Petersen.k2_high_witness
#print axioms Petersen.certified_distance
#print axioms Petersen.row11_false_0
#print axioms Petersen.row11_false_1
#print axioms Petersen.row11_false_2
#print axioms Petersen.row11_false_3
#print axioms Petersen.row11_false_4
#print axioms Petersen.row11_false_5
#print axioms Petersen.row11_false_6
#print axioms Petersen.row11_false_7
#print axioms Petersen.row11_false_8
#print axioms Petersen.row11_false_9
#print axioms Petersen.row11_false_10
#print axioms Petersen.row11_true_0
#print axioms Petersen.row11_true_1
#print axioms Petersen.row11_true_2
#print axioms Petersen.row11_true_3
#print axioms Petersen.row11_true_4
#print axioms Petersen.row11_true_5
#print axioms Petersen.row11_true_6
#print axioms Petersen.row11_true_7
#print axioms Petersen.row11_true_8
#print axioms Petersen.row11_true_9
#print axioms Petersen.row11_true_10
#print axioms Petersen.finite_rows11
#print axioms Petersen.finite_distance11
#print axioms Petersen.row12_false_0
#print axioms Petersen.row12_false_1
#print axioms Petersen.row12_false_2
#print axioms Petersen.row12_false_3
#print axioms Petersen.row12_false_4
#print axioms Petersen.row12_false_5
#print axioms Petersen.row12_false_6
#print axioms Petersen.row12_false_7
#print axioms Petersen.row12_false_8
#print axioms Petersen.row12_false_9
#print axioms Petersen.row12_false_10
#print axioms Petersen.row12_false_11
#print axioms Petersen.row12_true_0
#print axioms Petersen.row12_true_1
#print axioms Petersen.row12_true_2
#print axioms Petersen.row12_true_3
#print axioms Petersen.row12_true_4
#print axioms Petersen.row12_true_5
#print axioms Petersen.row12_true_6
#print axioms Petersen.row12_true_7
#print axioms Petersen.row12_true_8
#print axioms Petersen.row12_true_9
#print axioms Petersen.row12_true_10
#print axioms Petersen.row12_true_11
#print axioms Petersen.finite_rows12
#print axioms Petersen.finite_distance12
#print axioms Petersen.k2_sharp
#print axioms Petersen.k2_twelve
#print axioms Petersen.outer_two_small
#print axioms Petersen.inner_two_small
#print axioms Petersen.k2_main
#print axioms Petersen.eventual_nonbalance
#print axioms Petersen.inner_short_route
#print axioms Petersen.f_le_innerProfile
#print axioms Petersen.f_eq_zero_iff
#print axioms Petersen.mixed_balanced_of_imbalance
#print axioms Petersen.LDB_of_mixed
#print axioms Petersen.inner_zero_multiple
#print axioms Petersen.odd_f_bound
#print axioms Petersen.odd_f_max_unique
#print axioms Petersen.odd_f_center
#print axioms Petersen.odd_diameter
#print axioms Petersen.multiple_balanced_one
#print axioms Petersen.sharp_even
#print axioms Petersen.odd_antipode
#print axioms Petersen.odd_center_strip
#print axioms Petersen.odd_center_inner
#print axioms Petersen.odd_outer_count
#print axioms Petersen.odd_inner_count
#print axioms Petersen.odd_balanced_class
#print axioms Petersen.sharp_odd
#print axioms Petersen.k2_sharp_at
#print axioms Petersen.miklavic_sparl_4_4

#print Petersen.MiklavicSparl44
#print Petersen.miklavic_sparl_4_4
#check (Petersen.miklavic_sparl_4_4 : Petersen.MiklavicSparl44)
```

