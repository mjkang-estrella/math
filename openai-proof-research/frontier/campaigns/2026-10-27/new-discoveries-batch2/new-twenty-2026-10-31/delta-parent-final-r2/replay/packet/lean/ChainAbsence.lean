import ChainCases
import ChainTail3_1_2
import ChainTail3_1_6
import ChainTail3_8_2
import ChainTail3_8_6
import ChainTail6_1_3
import ChainTail6_1_4
import ChainTail6_8_3
import ChainTail6_8_4
namespace ChainPrefix
set_option linter.unusedSimpArgs false
theorem fits_left {xs ys : Es} (hf : Fits (xs ++ ys)) : Fits xs := by
  intro i j
  have hh := hf i j
  rw [pairCount_append] at hh
  omega

theorem no_prefix (a b c l m d v t f : V) (he : Literal.EndVertex Concrete.g7 a)
    (ha : v ≠ a) (hb : v ≠ b)
    (hf : Fits (first a b c l m ++ dbl b d ++ tri b v t ++ dbl v f)) : False := by
  have hfirst : Fits (first a b c l m) := fits_left hf
  have hd : Fits (first a b c l m ++ dbl b d) := fits_left (by simpa only [List.append_assoc] using hf)
  rcases end_options a he with rfl | rfl
  · rcases first3 l b c m hfirst with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩), (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    all_goals
      first
      | have hh := attach3_1_2 d hd; subst d; exact tail3_1_2 v t f ha hb hf
      | have hh := attach3_1_6 d hd; subst d; exact tail3_1_6 v t f ha hb hf
      | have hh := attach3_8_2 d hd; subst d; exact tail3_8_2 v t f ha hb hf
      | have hh := attach3_8_6 d hd; subst d; exact tail3_8_6 v t f ha hb hf
  · rcases first6 l b c m hfirst with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩), (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    all_goals
      first
      | have hh := attach6_1_3 d hd; subst d; exact tail6_1_3 v t f ha hb hf
      | have hh := attach6_1_4 d hd; subst d; exact tail6_1_4 v t f ha hb hf
      | have hh := attach6_8_3 d hd; subst d; exact tail6_8_3 v t f ha hb hf
      | have hh := attach6_8_4 d hd; subst d; exact tail6_8_4 v t f ha hb hf

theorem no_chain : ¬ Literal.HasChain Concrete.g7 := by
  rintro ⟨k,⟨ch⟩⟩
  rcases k with _ | _ | k
  · have hf := chain0_first ch
    have he := end_options (ch.base 0) ch.left_end
    have hr := end_options (ch.base 1) ch.right_end
    rcases he with he | he
    · rw [he] at hf
      rcases (first3 _ _ _ _ hf).1 with ⟨hb,_⟩ | ⟨hb,_⟩ <;> simp_all
    · rw [he] at hf
      rcases (first6 _ _ _ _ hf).1 with ⟨hb,_⟩ | ⟨hb,_⟩ <;> simp_all
  · exact no_prefix _ _ _ _ _ _ _ _ _ ch.left_end
      (fun hh => by have := ch.base_injective hh; norm_num at this)
      (fun hh => by have := ch.base_injective hh; norm_num at this) (chain1_prefix ch)
  · exact no_prefix _ _ _ _ _ _ _ _ _ ch.left_end
      (fun hh => by have := ch.base_injective hh; have ht := congrArg Fin.val this; norm_num [Nat.mod_eq_of_lt (by omega : 2 < k+1+1+2), Nat.mod_eq_of_lt (by omega : 1 < k+1+1+2)] at ht)
      (fun hh => by have := ch.base_injective hh; have ht := congrArg Fin.val this; norm_num [Nat.mod_eq_of_lt (by omega : 2 < k+1+1+2), Nat.mod_eq_of_lt (by omega : 1 < k+1+1+2)] at ht) (chain_long_prefix ch)
#print axioms no_chain
end ChainPrefix
