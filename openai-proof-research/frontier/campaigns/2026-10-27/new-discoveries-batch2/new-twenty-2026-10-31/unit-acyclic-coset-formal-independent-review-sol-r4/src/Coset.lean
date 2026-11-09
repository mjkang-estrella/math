import Bridges
noncomputable section
namespace UnitCoset
abbrev K := ZMod 3
abbrev Ambient := K × ZMod 2

def A : Finset Ambient := Finset.univ ×ˢ {1}
def H0 : Finset Ambient := Finset.univ ×ˢ {0}
@[simp] theorem mem_A (x : Ambient) : x ∈ A ↔ x.2 = 1 := by rcases x with ⟨u,v⟩; simp [A, eq_comm]
@[simp] theorem mem_H0 (x : Ambient) : x ∈ H0 ↔ x.2 = 0 := by rcases x with ⟨u,v⟩; simp [H0, eq_comm]
@[simp] theorem second (a : A) : (a : Ambient).2 = 1 := (mem_A _).mp a.property

def coord : K ≃ A where
  toFun u := ⟨(u,1), by simp⟩
  invFun a := (a : Ambient).1
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; exact Prod.ext rfl (second a).symm

@[simp] theorem coord_val (u : K) : (coord u : Ambient) = (u,1) := rfl
@[simp] theorem card_A : A.card = 3 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr coord]
  exact ZMod.card 3
@[simp] theorem card_H0 : H0.card = 3 := by simp [H0]
theorem card_ambient : Fintype.card Ambient = 6 := by norm_num [Ambient, K, Fintype.card_prod]
theorem nonempty_A : A.Nonempty := ⟨(0,1), by simp⟩
theorem standing_A : Standing A A := by
  refine ⟨nonempty_A, nonempty_A, rfl, ?_, ?_⟩
  · simp
  · intro a ha b hb
    have ha' := (mem_A a).mp ha
    have hb' := (mem_A b).mp hb
    simp only [mem_A, Prod.snd_add, ha', hb']
    decide

theorem admissible_all (f : A ≃ A) : Admissible A A f := by
  intro a
  exact standing_A.2.2.2.2 _ a.property _ (f a).property

@[simp] theorem sum_second (f : A ≃ A) (a : A) : (sumMap f a).2 = 0 := by
  simp [sumMap, second]; decide

def t : Ambient := (1,0)
def outputTranslation : A ≃ A where
  toFun a := ⟨(a : Ambient) + t, by simp [t]⟩
  invFun a := ⟨(a : Ambient) - t, by simp [t]⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

def translate (f : A ≃ A) : A ≃ A := f.trans outputTranslation
@[simp] theorem translate_val (f : A ≃ A) (a : A) :
    (translate f a : Ambient) = (f a : Ambient) + t := rfl

theorem translate_ne (f : A ≃ A) : translate f ≠ f := by
  intro h
  have he := congrArg (fun e : A ≃ A => (e (coord 0) : Ambient)) h
  have hz : t = 0 := add_left_cancel (he.trans (add_zero _).symm)
  have hone : (1 : K) = 0 := congrArg Prod.fst hz
  exact one_ne_zero hone

theorem fibre_translate (f : A ≃ A) (x : Ambient) :
    multiplicity (translate f) x = multiplicity f (x - t) := by
  unfold multiplicity
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (a : Ambient) + ((f a : Ambient) + t) = x ↔ _
  rw [← add_assoc, eq_sub_iff_add_eq]
  rfl

theorem indicator (f : A ≃ A) (hu : UnitSequence f) (x : Ambient) :
    multiplicity f x = if x.2 = 0 then 1 else 0 := by
  have hi := (unit_iff_injective f).mp hu
  let s : K → K := fun u => (sumMap f (coord u)).1
  have hs : Function.Injective s := by
    intro u v huv
    apply coord.injective
    apply hi
    exact Prod.ext huv ((sum_second f _).trans (sum_second f _).symm)
  by_cases hx : x.2 = 0
  · simp only [hx, ↓reduceIte]
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hs x.1
    have he : sumMap f (coord u) = x := Prod.ext hu ((sum_second f _).trans hx.symm)
    rw [← he]
    exact multiplicity_one f hi _
  · simp only [hx, ↓reduceIte]
    apply multiplicity_zero
    intro a he
    exact hx ((congrArg Prod.snd he).symm.trans (sum_second f a))

theorem translate_multiplicity (f : A ≃ A) (hu : UnitSequence f) :
    multiplicity (translate f) = multiplicity f := by
  funext x
  rw [fibre_translate, indicator f hu, indicator f hu]
  simp [t]

theorem no_acyclic_unit (f : A ≃ A) (hu : UnitSequence f) : ¬ Acyclic f := by
  intro hc
  exact translate_ne f (hc (translate f) (admissible_all _) (translate_multiplicity f hu))

theorem refutation : ¬ Conjecture := by
  intro h
  obtain ⟨f, _, hu, hc⟩ := h Ambient A A standing_A
  exact no_acyclic_unit f hu hc
end UnitCoset
