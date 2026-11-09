import MiddleBase
namespace R139.MiddleOCD
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
theorem bad_0 : ¬ IsOCD G8 (∅ : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ (∅ : Finset (Fin 8)) ∨ ∃ w ∈ (∅ : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_1 : ¬ IsOCD G8 ({0} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0} : Finset (Fin 8)) ∨ ∃ w ∈ ({0} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_2 : ¬ IsOCD G8 ({1} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1} : Finset (Fin 8)) ∨ ∃ w ∈ ({1} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_3 : ¬ IsOCD G8 ({2} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2} : Finset (Fin 8)) ∨ ∃ w ∈ ({2} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_4 : ¬ IsOCD G8 ({3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3} : Finset (Fin 8)) ∨ ∃ w ∈ ({3} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_5 : ¬ IsOCD G8 ({4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({4} : Finset (Fin 8)) ∨ ∃ w ∈ ({4} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_6 : ¬ IsOCD G8 ({5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({5} : Finset (Fin 8)) ∨ ∃ w ∈ ({5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_7 : ¬ IsOCD G8 ({6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({6} : Finset (Fin 8)) ∨ ∃ w ∈ ({6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_8 : ¬ IsOCD G8 ({7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({7} : Finset (Fin 8)) ∨ ∃ w ∈ ({7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_9 : ¬ IsOCD G8 ({0, 1} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 1} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 1} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_10 : ¬ IsOCD G8 ({0, 2} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 2} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 2} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_11 : ¬ IsOCD G8 ({0, 3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 3} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 3} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_12 : ¬ IsOCD G8 ({0, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 4} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_13 : ¬ IsOCD G8 ({0, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 5} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_14 : ¬ IsOCD G8 ({0, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_15 : ¬ IsOCD G8 ({0, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 7} : Finset (Fin 8)))ᶜ) (↑({1, 4, 5, 6} : Finset (Fin 8)))
    (by decide) 1 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_16 : ¬ IsOCD G8 ({1, 2} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({1, 2} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 2} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_17 : ¬ IsOCD G8 ({1, 3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({1, 3} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 3} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_18 : ¬ IsOCD G8 ({1, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 4} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_19 : ¬ IsOCD G8 ({1, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 5} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_20 : ¬ IsOCD G8 ({1, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_21 : ¬ IsOCD G8 ({1, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 7} : Finset (Fin 8)))ᶜ) (↑({0, 4, 5, 6} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_22 : ¬ IsOCD G8 ({2, 3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 3} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 3} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_23 : ¬ IsOCD G8 ({2, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 4} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_24 : ¬ IsOCD G8 ({2, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_25 : ¬ IsOCD G8 ({2, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({2, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_26 : ¬ IsOCD G8 ({2, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_27 : ¬ IsOCD G8 ({3, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({3, 4} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_28 : ¬ IsOCD G8 ({3, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({3, 5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_29 : ¬ IsOCD G8 ({3, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({3, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_30 : ¬ IsOCD G8 ({3, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({3, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_31 : ¬ IsOCD G8 ({4, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({4, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({4, 5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_32 : ¬ IsOCD G8 ({4, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({4, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({4, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_33 : ¬ IsOCD G8 ({4, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({4, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({4, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_34 : ¬ IsOCD G8 ({5, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({5, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({5, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_35 : ¬ IsOCD G8 ({5, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({5, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({5, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_36 : ¬ IsOCD G8 ({6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({6, 7} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_37 : ¬ IsOCD G8 ({0, 1, 2} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 1, 2} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 1, 2} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_38 : ¬ IsOCD G8 ({0, 1, 3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 1, 3} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 1, 3} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_39 : ¬ IsOCD G8 ({0, 1, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 1, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 1, 4} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_40 : ¬ IsOCD G8 ({0, 1, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 1, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 1, 5} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_41 : ¬ IsOCD G8 ({0, 1, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 1, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 1, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_42 : ¬ IsOCD G8 ({0, 1, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 1, 7} : Finset (Fin 8)))ᶜ) (↑({2, 3} : Finset (Fin 8)))
    (by decide) 2 4 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_43 : ¬ IsOCD G8 ({0, 2, 3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 2, 3} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 2, 3} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_44 : ¬ IsOCD G8 ({0, 2, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (5 ∈ ({0, 2, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 2, 4} : Finset (Fin 8)), G8.Adj 5 w)) (h.1 5)
theorem bad_45 : ¬ IsOCD G8 ({0, 2, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 2, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 2, 5} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_46 : ¬ IsOCD G8 ({0, 2, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 2, 6} : Finset (Fin 8)))ᶜ) (↑({1} : Finset (Fin 8)))
    (by decide) 1 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_47 : ¬ IsOCD G8 ({0, 2, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 2, 7} : Finset (Fin 8)))ᶜ) (↑({1, 4, 5, 6} : Finset (Fin 8)))
    (by decide) 1 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_48 : ¬ IsOCD G8 ({0, 3, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (5 ∈ ({0, 3, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 3, 4} : Finset (Fin 8)), G8.Adj 5 w)) (h.1 5)
theorem bad_49 : ¬ IsOCD G8 ({0, 3, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({0, 3, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 3, 5} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_50 : ¬ IsOCD G8 ({0, 3, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 3, 6} : Finset (Fin 8)))ᶜ) (↑({1} : Finset (Fin 8)))
    (by decide) 1 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_51 : ¬ IsOCD G8 ({0, 3, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 3, 7} : Finset (Fin 8)))ᶜ) (↑({1, 4, 5, 6} : Finset (Fin 8)))
    (by decide) 1 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_52 : ¬ IsOCD G8 ({0, 4, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 4, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 4, 5} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_53 : ¬ IsOCD G8 ({0, 4, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 4, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 4, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_54 : ¬ IsOCD G8 ({0, 4, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 4, 7} : Finset (Fin 8)))ᶜ) (↑({1, 5, 6} : Finset (Fin 8)))
    (by decide) 1 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_55 : ¬ IsOCD G8 ({0, 5, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0, 5, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({0, 5, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_56 : ¬ IsOCD G8 ({0, 5, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 5, 7} : Finset (Fin 8)))ᶜ) (↑({1, 4, 6} : Finset (Fin 8)))
    (by decide) 1 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_57 : ¬ IsOCD G8 ({0, 6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({0, 6, 7} : Finset (Fin 8)))ᶜ) (↑({1} : Finset (Fin 8)))
    (by decide) 1 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_58 : ¬ IsOCD G8 ({1, 2, 3} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({1, 2, 3} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 2, 3} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_59 : ¬ IsOCD G8 ({1, 2, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (5 ∈ ({1, 2, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 2, 4} : Finset (Fin 8)), G8.Adj 5 w)) (h.1 5)
theorem bad_60 : ¬ IsOCD G8 ({1, 2, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({1, 2, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 2, 5} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_61 : ¬ IsOCD G8 ({1, 2, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 2, 6} : Finset (Fin 8)))ᶜ) (↑({0} : Finset (Fin 8)))
    (by decide) 0 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_62 : ¬ IsOCD G8 ({1, 2, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 2, 7} : Finset (Fin 8)))ᶜ) (↑({0, 4, 5, 6} : Finset (Fin 8)))
    (by decide) 0 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_63 : ¬ IsOCD G8 ({1, 3, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (5 ∈ ({1, 3, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 3, 4} : Finset (Fin 8)), G8.Adj 5 w)) (h.1 5)
theorem bad_64 : ¬ IsOCD G8 ({1, 3, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (4 ∈ ({1, 3, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 3, 5} : Finset (Fin 8)), G8.Adj 4 w)) (h.1 4)
theorem bad_65 : ¬ IsOCD G8 ({1, 3, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 3, 6} : Finset (Fin 8)))ᶜ) (↑({0} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_66 : ¬ IsOCD G8 ({1, 3, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 3, 7} : Finset (Fin 8)))ᶜ) (↑({0, 4, 5, 6} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_67 : ¬ IsOCD G8 ({1, 4, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1, 4, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 4, 5} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_68 : ¬ IsOCD G8 ({1, 4, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1, 4, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 4, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_69 : ¬ IsOCD G8 ({1, 4, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 4, 7} : Finset (Fin 8)))ᶜ) (↑({0, 5, 6} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_70 : ¬ IsOCD G8 ({1, 5, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({1, 5, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({1, 5, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_71 : ¬ IsOCD G8 ({1, 5, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 5, 7} : Finset (Fin 8)))ᶜ) (↑({0, 4, 6} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_72 : ¬ IsOCD G8 ({1, 6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({1, 6, 7} : Finset (Fin 8)))ᶜ) (↑({0} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_73 : ¬ IsOCD G8 ({2, 3, 4} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 3, 4} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 3, 4} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_74 : ¬ IsOCD G8 ({2, 3, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 3, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 3, 5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_75 : ¬ IsOCD G8 ({2, 3, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({2, 3, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 4 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_76 : ¬ IsOCD G8 ({2, 3, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 3, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 3, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_77 : ¬ IsOCD G8 ({2, 4, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 4, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 4, 5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_78 : ¬ IsOCD G8 ({2, 4, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({2, 4, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_79 : ¬ IsOCD G8 ({2, 4, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 4, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 4, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_80 : ¬ IsOCD G8 ({2, 5, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({2, 5, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_81 : ¬ IsOCD G8 ({2, 5, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({2, 5, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({2, 5, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_82 : ¬ IsOCD G8 ({2, 6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({2, 6, 7} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 3 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_83 : ¬ IsOCD G8 ({3, 4, 5} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3, 4, 5} : Finset (Fin 8)) ∨ ∃ w ∈ ({3, 4, 5} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_84 : ¬ IsOCD G8 ({3, 4, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({3, 4, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_85 : ¬ IsOCD G8 ({3, 4, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3, 4, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({3, 4, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_86 : ¬ IsOCD G8 ({3, 5, 6} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({3, 5, 6} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_87 : ¬ IsOCD G8 ({3, 5, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({3, 5, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({3, 5, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_88 : ¬ IsOCD G8 ({3, 6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({3, 6, 7} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_89 : ¬ IsOCD G8 ({4, 5, 6} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({4, 5, 6} : Finset (Fin 8)) ∨ ∃ w ∈ ({4, 5, 6} : Finset (Fin 8)), G8.Adj 2 w)) (h.1 2)
theorem bad_90 : ¬ IsOCD G8 ({4, 5, 7} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (0 ∈ ({4, 5, 7} : Finset (Fin 8)) ∨ ∃ w ∈ ({4, 5, 7} : Finset (Fin 8)), G8.Adj 0 w)) (h.1 0)
theorem bad_91 : ¬ IsOCD G8 ({4, 6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({4, 6, 7} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
theorem bad_92 : ¬ IsOCD G8 ({5, 6, 7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 ((↑({5, 6, 7} : Finset (Fin 8)))ᶜ) (↑({0, 1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.2
def smallSets : List (Finset (Fin 8)) := [∅, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5}, {0, 6}, {0, 7}, {1, 2}, {1, 3}, {1, 4}, {1, 5}, {1, 6}, {1, 7}, {2, 3}, {2, 4}, {2, 5}, {2, 6}, {2, 7}, {3, 4}, {3, 5}, {3, 6}, {3, 7}, {4, 5}, {4, 6}, {4, 7}, {5, 6}, {5, 7}, {6, 7}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 1, 6}, {0, 1, 7}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 2, 7}, {0, 3, 4}, {0, 3, 5}, {0, 3, 6}, {0, 3, 7}, {0, 4, 5}, {0, 4, 6}, {0, 4, 7}, {0, 5, 6}, {0, 5, 7}, {0, 6, 7}, {1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 2, 6}, {1, 2, 7}, {1, 3, 4}, {1, 3, 5}, {1, 3, 6}, {1, 3, 7}, {1, 4, 5}, {1, 4, 6}, {1, 4, 7}, {1, 5, 6}, {1, 5, 7}, {1, 6, 7}, {2, 3, 4}, {2, 3, 5}, {2, 3, 6}, {2, 3, 7}, {2, 4, 5}, {2, 4, 6}, {2, 4, 7}, {2, 5, 6}, {2, 5, 7}, {2, 6, 7}, {3, 4, 5}, {3, 4, 6}, {3, 4, 7}, {3, 5, 6}, {3, 5, 7}, {3, 6, 7}, {4, 5, 6}, {4, 5, 7}, {4, 6, 7}, {5, 6, 7}]
theorem small_complete : ∀ S : Finset (Fin 8), S.card ≤ 3 → S ∈ smallSets := by decide
theorem ocd_G8_lower (S : Finset (Fin 8)) (h : IsOCD G8 S) : 4 ≤ S.card := by
  by_contra hn
  have hs := small_complete S (by omega)
  simp only [smallSets, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S; exact bad_0 h
  · subst S; exact bad_1 h
  · subst S; exact bad_2 h
  · subst S; exact bad_3 h
  · subst S; exact bad_4 h
  · subst S; exact bad_5 h
  · subst S; exact bad_6 h
  · subst S; exact bad_7 h
  · subst S; exact bad_8 h
  · subst S; exact bad_9 h
  · subst S; exact bad_10 h
  · subst S; exact bad_11 h
  · subst S; exact bad_12 h
  · subst S; exact bad_13 h
  · subst S; exact bad_14 h
  · subst S; exact bad_15 h
  · subst S; exact bad_16 h
  · subst S; exact bad_17 h
  · subst S; exact bad_18 h
  · subst S; exact bad_19 h
  · subst S; exact bad_20 h
  · subst S; exact bad_21 h
  · subst S; exact bad_22 h
  · subst S; exact bad_23 h
  · subst S; exact bad_24 h
  · subst S; exact bad_25 h
  · subst S; exact bad_26 h
  · subst S; exact bad_27 h
  · subst S; exact bad_28 h
  · subst S; exact bad_29 h
  · subst S; exact bad_30 h
  · subst S; exact bad_31 h
  · subst S; exact bad_32 h
  · subst S; exact bad_33 h
  · subst S; exact bad_34 h
  · subst S; exact bad_35 h
  · subst S; exact bad_36 h
  · subst S; exact bad_37 h
  · subst S; exact bad_38 h
  · subst S; exact bad_39 h
  · subst S; exact bad_40 h
  · subst S; exact bad_41 h
  · subst S; exact bad_42 h
  · subst S; exact bad_43 h
  · subst S; exact bad_44 h
  · subst S; exact bad_45 h
  · subst S; exact bad_46 h
  · subst S; exact bad_47 h
  · subst S; exact bad_48 h
  · subst S; exact bad_49 h
  · subst S; exact bad_50 h
  · subst S; exact bad_51 h
  · subst S; exact bad_52 h
  · subst S; exact bad_53 h
  · subst S; exact bad_54 h
  · subst S; exact bad_55 h
  · subst S; exact bad_56 h
  · subst S; exact bad_57 h
  · subst S; exact bad_58 h
  · subst S; exact bad_59 h
  · subst S; exact bad_60 h
  · subst S; exact bad_61 h
  · subst S; exact bad_62 h
  · subst S; exact bad_63 h
  · subst S; exact bad_64 h
  · subst S; exact bad_65 h
  · subst S; exact bad_66 h
  · subst S; exact bad_67 h
  · subst S; exact bad_68 h
  · subst S; exact bad_69 h
  · subst S; exact bad_70 h
  · subst S; exact bad_71 h
  · subst S; exact bad_72 h
  · subst S; exact bad_73 h
  · subst S; exact bad_74 h
  · subst S; exact bad_75 h
  · subst S; exact bad_76 h
  · subst S; exact bad_77 h
  · subst S; exact bad_78 h
  · subst S; exact bad_79 h
  · subst S; exact bad_80 h
  · subst S; exact bad_81 h
  · subst S; exact bad_82 h
  · subst S; exact bad_83 h
  · subst S; exact bad_84 h
  · subst S; exact bad_85 h
  · subst S; exact bad_86 h
  · subst S; exact bad_87 h
  · subst S; exact bad_88 h
  · subst S; exact bad_89 h
  · subst S; exact bad_90 h
  · subst S; exact bad_91 h
  · subst S; exact bad_92 h
theorem ocd'_G8_lower (S : Finset (Fin 8)) (h : IsOCD' G8 S) : 4 ≤ S.card := ocd_G8_lower S ⟨h.1, h.2.preconnected⟩
end R139.MiddleOCD
