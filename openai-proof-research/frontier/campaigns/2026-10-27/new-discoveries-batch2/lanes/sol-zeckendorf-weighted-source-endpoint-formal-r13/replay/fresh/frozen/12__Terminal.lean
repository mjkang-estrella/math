import Literal
import Mathlib.Data.Multiset.Sort
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

theorem sorted_gap (l : List ℕ) (hp : Positive (l : Board))
 (ht : BinaryNonadjacent (l : Board)) (hs : l.Pairwise (· ≥ ·)) :
 l.Pairwise (fun a b => b+2 ≤ a) := by
 induction l with
 | nil => simp
 | cons a l ih =>
   rw [List.pairwise_cons] at hs ⊢
   have hsub : (l : Board) ≤ ((a::l : List ℕ) : Board) := by
     exact Multiset.le_cons_self _ _
   refine ⟨?_,ih (fun i hi => hp i (Multiset.mem_of_le hsub hi))
     ⟨fun i hi h => ht.1 i hi (h.trans hsub),
      fun i hi h => ht.2 i hi (h.trans hsub)⟩ hs.2⟩
   intro j hj
   have hjp : 1 ≤ j := hp j (by simp [hj])
   have hja := hs.1 j hj
   have hpair : ({a,j} : Board) ≤ ((a::l : List ℕ) : Board) := by
     have hh : ({j} : Board) ≤ (l : Board) := Multiset.singleton_le.mpr hj
     exact Multiset.cons_le_cons a hh
   have hne : a ≠ j := by
     intro h; subst a; exact ht.1 j hjp hpair
   have hna : a ≠ j+1 := by
     intro h; subst a
     apply ht.2 j hjp
     rw [Multiset.pair_comm]
     exact hpair
   omega

def sourceIndices (b : Board) : List ℕ := (b.sort (· ≥ ·)).map (· + 1)
def Z (N : ℕ) : ℕ := (Nat.zeckendorf N).length

theorem terminal_rep (b : Board) (hp : Positive b) (ht : Terminal b) :
 (sourceIndices b).IsZeckendorfRep := by
 have hg := sorted_gap (b.sort (· ≥ ·)) (by simpa using hp)
   (by simpa using (terminal_iff b).mp ht) (Multiset.pairwise_sort _ _)
 have hp' : ∀ i ∈ b.sort (· ≥ ·), 1 ≤ i := by simpa [Positive] using hp
 unfold sourceIndices List.IsZeckendorfRep
 apply List.Pairwise.isChain
 rw [List.pairwise_append]
 refine ⟨?_,by simp,?_⟩
 · rw [List.pairwise_map]
   exact hg.imp (by intros; omega)
 · intro a ha c hc
   obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
   have hc' : c = 0 := by simpa using hc
   subst c
   have := hp' i hi
   omega

theorem sourceIndices_value (b : Board) :
 ((sourceIndices b).map Nat.fib).sum = value b := by
 have h := congrArg (fun s : Board => (s.map F).sum) (Multiset.sort_eq b (· ≥ ·))
 change ((sourceIndices b).map Nat.fib).sum = (b.map F).sum
 rw [Multiset.map_coe,Multiset.sum_coe] at h
 unfold sourceIndices
 rw [List.map_map]
 have hf : Nat.fib ∘ (fun x : ℕ => x+1) = F := funext (fun _ => rfl)
 rw [hf]
 exact h

theorem terminal_eq_zeckendorf (b : Board) (hp : Positive b) (ht : Terminal b) :
 sourceIndices b = Nat.zeckendorf (value b) := by
 rw [← sourceIndices_value b]
 exact (Nat.zeckendorf_sum_fib (terminal_rep b hp ht)).symm

theorem terminal_card (b : Board) (hp : Positive b) (ht : Terminal b) :
 b.card = Z (value b) := by
 have := congrArg List.length (terminal_eq_zeckendorf b hp ht)
 simpa [sourceIndices,Z] using this

theorem complete_combine_count {N : ℕ} {ms : List Move} {b : Board}
 (he : Executes (initial N) ms b) (ht : Terminal b) :
 (ms.map combine).sum = N - Z N := by
 rw [all_word_combine_count he,terminal_card b
   (executes_positive he (initial_positive N)) ht,← executes_value he,initial_value]

theorem sourceIndices_inverse (b : Board) :
 (((sourceIndices b).map (fun i => i-1) : List ℕ) : Board) = b := by
 simp [sourceIndices,List.map_map,Function.comp_def,Multiset.sort_eq]

theorem terminal_unique {a b : Board} (ha : Positive a) (hb : Positive b)
 (hta : Terminal a) (htb : Terminal b) (hv : value a = value b) : a = b := by
 have h : sourceIndices a = sourceIndices b := by
   rw [terminal_eq_zeckendorf a ha hta,terminal_eq_zeckendorf b hb htb,hv]
 rw [← sourceIndices_inverse a,← sourceIndices_inverse b,h]
end LiteralGame
