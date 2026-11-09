import CMDRROccurrence
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin

open scoped Classical
namespace CMDRR
variable {M W O : Type} [Fintype O]

def Cell (s : Matching M W) := {p : M × W // ¬ s.spouse p.1 p.2}
def Incidence (d : Schedule M W O) := Σ o, {p : M × W // p ∈ (d.game o).teams}

namespace Source
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)

def incidenceCell (x : Incidence d) : Cell s :=
  ⟨x.2.1, h.allowed x.2.2⟩

 theorem incidenceCell_bijective : Function.Bijective h.incidenceCell := by
  constructor
  · rintro ⟨o,a,ha⟩ ⟨p,b,hb⟩ he
    have hab : a = b := congrArg Subtype.val he
    have hop : o = p := h.occurrence_eq ha (hab ▸ hb)
    subst p
    subst b
    rfl
  · rintro ⟨⟨m,w⟩,ha⟩
    obtain ⟨o,ho,_⟩ := h.partnership_unique ha
    exact ⟨⟨o,⟨(m,w),ho⟩⟩,rfl⟩

noncomputable def cellsEquiv : Incidence d ≃ Cell s :=
  Equiv.ofBijective h.incidenceCell h.incidenceCell_bijective
end Source

namespace Game
variable (g : Game M W)
noncomputable def other (a : {p // p ∈ g.teams}) : {p // p ∈ g.teams} :=
  ⟨(g.opposite_unique a.2).choose, (g.opposite_unique a.2).choose_spec.1.1⟩

 theorem other_ne (a : {p // p ∈ g.teams}) : g.other a ≠ a := by
  intro he
  exact (g.opposite_unique a.2).choose_spec.1.2 (congrArg Subtype.val he)

 theorem other_other (a : {p // p ∈ g.teams}) : g.other (g.other a) = a := by
  apply Subtype.ext
  symm
  apply (g.opposite_unique (g.other a).2).choose_spec.2
  exact ⟨a.2, fun he => g.other_ne a (Subtype.ext he.symm)⟩

noncomputable def exchange : Equiv.Perm {p // p ∈ g.teams} where
  toFun := g.other
  invFun := g.other
  left_inv := g.other_other
  right_inv := g.other_other

 theorem other_male_ne (a : {p // p ∈ g.teams}) :
    (g.other a).1.1 ≠ a.1.1 :=
  g.men_distinct _ (g.other a).2 _ a.2 (fun e => g.other_ne a (Subtype.ext e))

 theorem other_female_ne (a : {p // p ∈ g.teams}) :
    (g.other a).1.2 ≠ a.1.2 :=
  g.women_distinct _ (g.other a).2 _ a.2 (fun e => g.other_ne a (Subtype.ext e))
end Game

namespace Schedule
variable (d : Schedule M W O)
noncomputable def exchange : Equiv.Perm (Incidence d) where
  toFun x := ⟨x.1,(d.game x.1).other x.2⟩
  invFun x := ⟨x.1,(d.game x.1).other x.2⟩
  left_inv := by rintro ⟨o,a⟩; exact congrArg (Sigma.mk o) ((d.game o).other_other a)
  right_inv := by rintro ⟨o,a⟩; exact congrArg (Sigma.mk o) ((d.game o).other_other a)

 omit [Fintype O] in
 theorem exchange_ne (x : Incidence d) : d.exchange x ≠ x := by
  rcases x with ⟨o,a⟩
  intro he
  have : (d.game o).other a = a := by
    exact eq_of_heq (Sigma.mk.inj he).2
  exact (d.game o).other_ne a this
end Schedule

namespace Source
variable {s : Matching M W} {d : Schedule M W O} (h : Source s d)
/-- The actual opposite-team permutation on allowed partnership cells. -/
noncomputable def T : Equiv.Perm (Cell s) :=
  h.cellsEquiv.symm.trans (d.exchange.trans h.cellsEquiv)

 theorem T_involutive : Function.Involutive h.T := by
  intro x
  change h.cellsEquiv (d.exchange (h.cellsEquiv.symm
    (h.cellsEquiv (d.exchange (h.cellsEquiv.symm x))))) = x
  rw [Equiv.symm_apply_apply]
  have hex : ∀ a, d.exchange (d.exchange a) = a := by
    rintro ⟨o,a⟩
    exact congrArg (Sigma.mk o) ((d.game o).other_other a)
  rw [hex, Equiv.apply_symm_apply]

 theorem T_fixedPointFree (x : Cell s) : h.T x ≠ x := by
  intro he
  have he' := congrArg h.cellsEquiv.symm he
  have : d.exchange (h.cellsEquiv.symm x) = h.cellsEquiv.symm x := by
    simpa only [T, Equiv.trans_apply, Equiv.symm_apply_apply] using he'
  exact d.exchange_ne _ this
end Source
end CMDRR
