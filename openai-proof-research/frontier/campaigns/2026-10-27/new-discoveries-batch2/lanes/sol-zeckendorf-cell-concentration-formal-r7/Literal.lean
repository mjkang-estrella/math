import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Data.Multiset.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

abbrev Board := Multiset ℕ
def F (i : ℕ) : ℕ := Nat.fib (i+1)
def w (i : ℕ) : ℤ := (i:ℤ)+2+2*(F i:ℤ)-(F (i+1):ℤ)
def value (b : Board) : ℕ := (b.map F).sum
def potential (b : Board) : ℤ := (b.map w).sum
def Positive (b : Board) : Prop := ∀ i ∈ b, 1 ≤ i

-- Ck k is source C_(k+2); Sk k is source S_(k+3).
inductive Move where
 | C1 | Ck (k : ℕ) | S2 | Sk (k : ℕ)
 deriving DecidableEq

def input : Move → Board
 | .C1 => {1,1}
 | .Ck k => {k+1,k+2}
 | .S2 => {2,2}
 | .Sk k => {k+3,k+3}
def output : Move → Board
 | .C1 => {2}
 | .Ck k => {k+3}
 | .S2 => {1,3}
 | .Sk k => {k+1,k+4}
def drop : Move → ℕ
 | .C1 => 1
 | .Ck k => k+2
 | .S2 | .Sk _ => 1
def combine : Move → ℕ
 | .C1 | .Ck _ => 1
 | .S2 | .Sk _ => 0
def Step (b : Board) (m : Move) (c : Board) : Prop :=
 ∃ r : Board, b = r + input m ∧ c = r + output m
inductive Executes : Board → List Move → Board → Prop
 | nil (b : Board) : Executes b [] b
 | cons {a b c : Board} {m : Move} {ms : List Move} :
     Step a m b → Executes b ms c → Executes a (m::ms) c

theorem F_rec (i : ℕ) : F (i+2) = F i + F (i+1) := by
 simpa [F, Nat.add_assoc] using (Nat.fib_add_two (n:=i+1))
theorem F_mono (i : ℕ) : F i ≤ F (i+1) := Nat.fib_mono (by omega)
theorem w_pos (i : ℕ) (hi : 1 ≤ i) : 0 < w i := by
 obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
 have h := F_rec j
 have h' := F_mono j
 dsimp [w]
 simp only [Nat.add_comm 1 j, Nat.add_assoc] at *
 norm_num at *
 omega

@[simp] theorem value_add (a b : Board) : value (a+b) = value a + value b := by
 simp [value]
@[simp] theorem potential_add (a b : Board) : potential (a+b) = potential a + potential b := by
 simp [potential]
theorem move_value (m : Move) : value (input m) = value (output m) := by
 cases m with
 | C1 => norm_num [value,input,output,F,Nat.fib_add_two]
 | S2 => norm_num [value,input,output,F,Nat.fib_add_two]
 | Ck k => simpa [value,input,output] using (F_rec (k+1)).symm
 | Sk k =>
   have a := F_rec (k+1)
   have b := F_rec (k+2)
   simp [value,input,output]
   simp only [Nat.add_assoc] at *
   norm_num at *
   omega
theorem move_potential (m : Move) :
 potential (input m) = potential (output m) + (drop m:ℤ) := by
 cases m with
 | C1 => norm_num [potential,input,output,drop,w,F,Nat.fib_add_two]
 | S2 => norm_num [potential,input,output,drop,w,F,Nat.fib_add_two]
 | Ck k =>
   have a := F_rec (k+1)
   have b := F_rec (k+2)
   simp [potential,input,output,drop,w]
   simp only [Nat.add_assoc] at *
   norm_num at *
   omega
 | Sk k =>
   have a := F_rec (k+1)
   have b := F_rec (k+2)
   have c := F_rec (k+3)
   simp [potential,input,output,drop,w]
   simp only [Nat.add_assoc] at *
   norm_num at *
   omega
theorem move_tokens (m : Move) : (input m).card = (output m).card + combine m := by
 cases m <;> simp [input,output,combine]
theorem step_value {a b : Board} {m : Move} (h : Step a m b) : value a = value b := by
 obtain ⟨r,rfl,rfl⟩ := h
 simp [move_value]
theorem step_potential {a b : Board} {m : Move} (h : Step a m b) :
 potential a = potential b + (drop m:ℤ) := by
 obtain ⟨r,rfl,rfl⟩ := h
 simp only [potential_add,move_potential]
 omega
theorem step_tokens {a b : Board} {m : Move} (h : Step a m b) :
 a.card = b.card + combine m := by
 obtain ⟨r,rfl,rfl⟩ := h
 simp only [Multiset.card_add,move_tokens]
 omega
theorem step_positive {a b : Board} {m : Move} (h : Step a m b)
 (ha : Positive a) : Positive b := by
 obtain ⟨r,rfl,rfl⟩ := h
 intro i hi
 rcases Multiset.mem_add.mp hi with hi | hi
 · exact ha i (Multiset.mem_add.mpr (Or.inl hi))
 · cases m <;> simp [output] at hi <;> omega
theorem executes_value {a b : Board} {ms : List Move} (h : Executes a ms b) :
 value a = value b := by
 induction h with
 | nil => rfl
 | cons h _ ih => exact (step_value h).trans ih
theorem executes_positive {a b : Board} {ms : List Move} (h : Executes a ms b)
 (ha : Positive a) : Positive b := by
 induction h with
 | nil => exact ha
 | cons h _ ih => exact ih (step_positive h ha)
theorem executes_potential {a b : Board} {ms : List Move} (h : Executes a ms b) :
 potential a = potential b + ((ms.map drop).sum:ℤ) := by
 induction h with
 | nil => simp
 | cons h _ ih => simp only [List.map_cons,List.sum_cons,Nat.cast_add]; linarith [step_potential h]
theorem executes_tokens {a b : Board} {ms : List Move} (h : Executes a ms b) :
 a.card = b.card + (ms.map combine).sum := by
 induction h with
 | nil => simp
 | cons h _ ih =>
   have ht := step_tokens h
   simp only [List.map_cons,List.sum_cons]
   omega

theorem potential_nonneg {b : Board} (hb : Positive b) : 0 ≤ potential b := by
 induction b using Multiset.induction_on with
 | empty => simp [potential]
 | @cons i b ih =>
   have hi := hb i (by simp)
   have hr : Positive b := fun j hj => hb j (by simp [hj])
   have hw := w_pos i hi
   have hn := ih hr
   simpa [potential] using add_nonneg (le_of_lt hw) hn
theorem potential_pos {b : Board} (hb : Positive b) (hv : 0 < value b) :
 0 < potential b := by
 induction b using Multiset.induction_on with
 | empty => simp [value] at hv
 | @cons i b ih =>
   have hi := hb i (by simp)
   have hr : Positive b := fun j hj => hb j (by simp [hj])
   have hw := w_pos i hi
   have hn := potential_nonneg hr
   simpa [potential] using add_pos_of_pos_of_nonneg hw hn
theorem support_bound {b : Board} {i : ℕ} (hi : i ∈ b) : i ≤ value b := by
 have hf := Nat.le_fib_add_one (i+1)
 have hs : F i ≤ value b := by
   induction b using Multiset.induction_on with
   | empty => simp at hi
   | @cons j b ih =>
     simp only [Multiset.mem_cons] at hi
     simp only [value,Multiset.map_cons,Multiset.sum_cons]
     rcases hi with rfl | hi
     · omega
     · have h := ih hi; dsimp [value] at h; omega
 dsimp [F] at hs
 omega
def initial (N : ℕ) : Board := Multiset.replicate N 1
@[simp] theorem initial_value (N : ℕ) : value (initial N) = N := by
 simp [initial,value,F,Nat.fib_add_two]
@[simp] theorem initial_potential (N : ℕ) : potential (initial N) = 3*(N:ℤ) := by
 simp [initial,potential,w,F,Nat.fib_add_two]
 omega
theorem initial_positive (N : ℕ) : Positive (initial N) := by
 intro i hi
 have : i=1 := (Multiset.mem_replicate.mp hi).2
 omega
theorem length_le_drop (ms : List Move) : ms.length ≤ (ms.map drop).sum := by
 induction ms with
 | nil => simp
 | cons m ms ih =>
   have hm : 1 ≤ drop m := by cases m <;> simp [drop]
   simp only [List.length_cons,List.map_cons,List.sum_cons]
   omega
theorem all_prefix_length_lt {N : ℕ} (hN : 0 < N) {ms : List Move} {b : Board}
 (h : Executes (initial N) ms b) : ms.length < 3*N := by
 have hv := executes_value h
 have hp := executes_positive h (initial_positive N)
 have hw := executes_potential h
 have hx := potential_pos hp (by rw [← hv, initial_value]; exact hN)
 have hl := length_le_drop ms
 simp only [initial_value] at hv
 simp only [initial_potential] at hw
 omega
theorem all_word_combine_count {N : ℕ} {ms : List Move} {b : Board}
 (h : Executes (initial N) ms b) : (ms.map combine).sum = N-b.card := by
 have ht := executes_tokens h
 simp only [initial,Multiset.card_replicate] at ht
 omega

def Terminal (b : Board) : Prop := ∀ m c, ¬ Step b m c
def BinaryNonadjacent (b : Board) : Prop :=
 (∀ i, 1 ≤ i → ¬ ({i,i} : Board) ≤ b) ∧
 (∀ i, 1 ≤ i → ¬ ({i,i+1} : Board) ≤ b)
theorem has_step_iff (b : Board) (m : Move) :
 (∃ c, Step b m c) ↔ input m ≤ b := by
 constructor
 · rintro ⟨c,r,h,_⟩
   rw [h]
   exact Multiset.le_add_left _ _
 · intro h
   obtain ⟨r,hr⟩ := Multiset.le_iff_exists_add.mp h
   exact ⟨r+output m,r,by simpa [add_comm] using hr,rfl⟩
theorem terminal_iff (b : Board) : Terminal b ↔ BinaryNonadjacent b := by
 have ht : Terminal b ↔ ∀ m, ¬ input m ≤ b := by
   simp only [Terminal,← not_exists,has_step_iff]
 rw [ht]
 constructor
 · intro h
   constructor
   · intro i hi
     match i with
     | 0 => omega
     | 1 => exact h .C1
     | 2 => exact h .S2
     | k+3 => exact h (.Sk k)
   · intro i hi
     obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hi
     simpa [input,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h (.Ck k)
 · rintro ⟨hd,ha⟩ m
   cases m with
   | C1 => exact hd 1 (by omega)
   | S2 => exact hd 2 (by omega)
   | Ck k => simpa [input,Nat.add_assoc] using ha (k+1) (by omega)
   | Sk k => exact hd (k+3) (by omega)
theorem exists_complete (b : Board) (hb : Positive b) :
 ∃ ms c, Executes b ms c ∧ Terminal c := by
 classical
 suffices hh : ∀ n b, Positive b → (potential b).toNat = n →
     ∃ ms c, Executes b ms c ∧ Terminal c from hh _ b hb rfl
 intro n
 induction n using Nat.strong_induction_on with
 | h n ih =>
   intro b hb hn
   by_cases ht : Terminal b
   · exact ⟨[],b,Executes.nil b,ht⟩
   · simp only [Terminal,not_forall,not_not] at ht
     obtain ⟨m,c,hstep⟩ := ht
     have hc := step_positive hstep hb
     have hpc := potential_nonneg hc
     have hpb := potential_nonneg hb
     have he := step_potential hstep
     have hd : 0 < drop m := by cases m <;> simp [drop]
     have hlt : (potential c).toNat < n := by omega
     obtain ⟨ms,d,hm,ht⟩ := ih _ hlt c hc rfl
     exact ⟨m::ms,d,Executes.cons hstep hm,ht⟩
theorem initial_has_complete (N : ℕ) :
 ∃ ms c, Executes (initial N) ms c ∧ Terminal c := exists_complete _ (initial_positive N)

theorem step_deterministic {b c d : Board} {m : Move}
 (hc : Step b m c) (hd : Step b m d) : c=d := by
 obtain ⟨r,hr,rfl⟩ := hc
 obtain ⟨s,hs,rfl⟩ := hd
 have : r=s := add_right_cancel (hr.symm.trans hs)
 rw [this]
theorem executes_deterministic {b c d : Board} {ms : List Move}
 (hc : Executes b ms c) (hd : Executes b ms d) : c=d := by
 induction hc generalizing d with
 | nil => cases hd; rfl
 | cons hs he ih =>
   cases hd with
   | cons ht hw =>
     have hh := step_deterministic hs ht
     subst hh
     exact ih hw

def alphabet (N : ℕ) : Finset Move :=
 {Move.C1,Move.S2} ∪ ((Finset.range (N+1)).image Move.Ck ∪
   (Finset.range (N+1)).image Move.Sk)
theorem step_in_alphabet {b c : Board} {m : Move} (h : Step b m c) :
 m ∈ alphabet (value b) := by
 have hl := (has_step_iff b m).mp ⟨c,h⟩
 cases m with
 | C1 => simp [alphabet]
 | S2 => simp [alphabet]
 | Ck k =>
   have hm : k+2 ∈ b := Multiset.mem_of_le hl (by simp [input])
   have hk := support_bound hm
   simp only [alphabet,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
     Finset.mem_image,Finset.mem_range]
   exact Or.inr (Or.inl ⟨k,by omega,rfl⟩)
 | Sk k =>
   have hm : k+3 ∈ b := Multiset.mem_of_le hl (by simp [input])
   have hk := support_bound hm
   simp only [alphabet,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
     Finset.mem_image,Finset.mem_range]
   exact Or.inr (Or.inr ⟨k,by omega,rfl⟩)
noncomputable def words (N : ℕ) : ℕ → Finset (List Move)
 | 0 => {[]}
 | n+1 => {[]} ∪ (alphabet N).biUnion (fun m => (words N n).image (List.cons m))
theorem mem_words {N n : ℕ} {ms : List Move}
 (hl : ms.length ≤ n) (ha : ∀ m ∈ ms, m ∈ alphabet N) : ms ∈ words N n := by
 induction n generalizing ms with
 | zero => have : ms=[] := List.length_eq_zero_iff.mp (by omega); subst ms; simp [words]
 | succ n ih =>
   cases ms with
   | nil => simp [words]
   | cons m ms =>
     have hm := ha m (by simp)
     have ht := ih (by simpa using Nat.le_of_succ_le_succ hl)
       (fun x hx => ha x (by simp [hx]))
     simp only [words,Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_image]
     exact Or.inr ⟨m,hm,ms,ht,rfl⟩
theorem executes_alphabet {b c : Board} {ms : List Move} (h : Executes b ms c) :
 ∀ m ∈ ms, m ∈ alphabet (value b) := by
 induction h with
 | nil => simp
 | cons hs he ih =>
   intro m hm
   simp only [List.mem_cons] at hm
   rcases hm with rfl | hm
   · exact step_in_alphabet hs
   · rw [step_value hs]; exact ih m hm
theorem all_words_in_finite_language {N : ℕ} (hN : 0 < N)
 {ms : List Move} {b : Board} (h : Executes (initial N) ms b) :
 ms ∈ words N (3*N) := by
 apply mem_words (Nat.le_of_lt (all_prefix_length_lt hN h))
 simpa only [initial_value] using executes_alphabet h
def completeWords (N : ℕ) : Set (List Move) :=
 {ms | ∃ b, Executes (initial N) ms b ∧ Terminal b}
theorem completeWords_nonempty (N : ℕ) : (completeWords N).Nonempty := by
 obtain ⟨ms,c,he,ht⟩ := initial_has_complete N
 exact ⟨ms,c,he,ht⟩
theorem completeWords_finite (N : ℕ) (hN : 0 < N) : (completeWords N).Finite := by
 apply (words N (3*N)).finite_toSet.subset
 rintro ms ⟨b,he,ht⟩
 exact all_words_in_finite_language hN he

end LiteralGame
