import Mathlib.Tactic

namespace Supervenience

inductive Form (n : Nat) where
  | atom : Nat → Form n
  | neg : Form n → Form n
  | conj : Form n → Form n → Form n
  | dep : (Fin n → Form n) → Form n → Form n

structure Model (W : Type) where
  edge : W → W → W → Prop
  val : W → Nat → Prop

noncomputable def eval {n : Nat} {W : Type} (M : Model W) : Form n → W → Prop
  | .atom a, w => M.val w a
  | .neg f, w => ¬ eval M f w
  | .conj f g, w => eval M f w ∧ eval M g w
  | .dep a b, w => ∀ u v, M.edge w u v →
      (∀ i, eval M (a i) u ↔ eval M (a i) v) → (eval M b u ↔ eval M b v)

def unary (a b : Form 1) : Form 1 := .dep (fun _ => a) b

def gate (a b : Form 1) : Form 1 := unary a (.conj a b)

def split (a b c : Form 1) : Form 1 :=
 .conj (.conj (gate (.conj a b) c) (gate (.conj a (.neg b)) c))
       (.conj (gate (.conj (.neg a) b) c) (gate (.conj (.neg a) (.neg b)) c))

theorem gate_eval {W : Type} (M : Model W) (a b : Form 1) (w : W) :
 eval M (gate a b) w ↔ ∀ u v, M.edge w u v → eval M a u → eval M a v →
 (eval M b u ↔ eval M b v) := by
 simp only [gate, unary, eval]
 constructor
 · intro h u v huv hau hav
   have hh := h u v huv (fun _ => ⟨fun _ => hav, fun _ => hau⟩)
   tauto
 · intro h u v huv ha
   have haa := ha 0
   constructor
   · rintro ⟨hau, hbu⟩
     have hav := haa.mp hau
     exact ⟨hav, (h u v huv hau hav).mp hbu⟩
   · rintro ⟨hav, hbv⟩
     have hau := haa.mpr hav
     exact ⟨hau, (h u v huv hau hav).mpr hbv⟩

theorem split_eval {W : Type} (M : Model W) (a b c : Form 1) (w : W) :
 eval M (split a b c) w ↔ ∀ u v, M.edge w u v →
 (eval M a u ↔ eval M a v) → (eval M b u ↔ eval M b v) →
 (eval M c u ↔ eval M c v) := by
 classical
 simp only [split, eval, gate_eval]
 constructor
 · rintro ⟨⟨h00,h01⟩,h10,h11⟩ u v huv ha hb
   by_cases hau : eval M a u <;> by_cases hbu : eval M b u
   · exact h00 u v huv ⟨hau,hbu⟩ ⟨ha.mp hau,hb.mp hbu⟩
   · exact h01 u v huv ⟨hau,hbu⟩ ⟨ha.mp hau,fun h => hbu (hb.mpr h)⟩
   · exact h10 u v huv ⟨hau,hbu⟩ ⟨fun h => hau (ha.mpr h),hb.mp hbu⟩
   · exact h11 u v huv ⟨hau,hbu⟩ ⟨fun h => hau (ha.mpr h),fun h => hbu (hb.mpr h)⟩
 · intro h
   refine ⟨⟨?_,?_⟩,?_,?_⟩ <;> intro u v huv hu hv <;>
    apply h u v huv <;> tauto

noncomputable def translate : Form 2 → Form 1
 | .atom a => .atom a
 | .neg f => .neg (translate f)
 | .conj f g => .conj (translate f) (translate g)
 | .dep a b => split (translate (a 0)) (translate (a 1)) (translate b)

theorem translate_correct {W : Type} (M : Model W) (f : Form 2) (w : W) :
 eval M (translate f) w ↔ eval M f w := by
 induction f generalizing w with
 | atom a => rfl
 | neg f ih => exact not_congr (ih w)
 | conj f g ihf ihg => exact and_congr (ihf w) (ihg w)
 | dep a b iha ihb =>
   simp only [translate, split_eval, eval, iha, ihb]
   constructor
   · intro h u v huv ha
     exact h u v huv (ha 0) (ha 1)
   · intro h u v huv h0 h1
     apply h u v huv
     intro i
     fin_cases i <;> assumption

-- The strictness claim at n = 1 requires an L_2 formula without any L_1 equivalent.
-- This definition quantifies over all types of worlds and all ternary-frame models.
def StrictAtOne : Prop := ∃ f : Form 2, ∀ g : Form 1,
 ¬ (∀ (W : Type) (M : Model W) (w : W), eval M g w ↔ eval M f w)

theorem hierarchy_conjecture_false : ¬ StrictAtOne := by
 rintro ⟨f,hf⟩
 exact hf (translate f) (fun _ M w => translate_correct M f w)

def StrictStep (n : Nat) : Prop := ∃ f : Form (n + 1), ∀ g : Form n,
 ¬ (∀ (W : Type) (M : Model W) (w : W), eval M g w ↔ eval M f w)

def HierarchyConjecture : Prop := ∀ n : Nat, StrictStep n

theorem literal_conjecture_false : ¬ HierarchyConjecture := by
 intro h
 exact hierarchy_conjecture_false (h 1)

#print axioms literal_conjecture_false
end Supervenience
