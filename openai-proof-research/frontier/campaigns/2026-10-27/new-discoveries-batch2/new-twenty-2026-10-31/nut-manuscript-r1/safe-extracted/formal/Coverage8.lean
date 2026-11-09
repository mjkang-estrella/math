import CatalogueInduction
import NutInterface
import CatalogueClosure1
import CatalogueClosure2
import CatalogueClosure3
import CatalogueClosure4
import CatalogueClosure5
import CatalogueClosure6
import CatalogueClosure7
namespace Nut8
theorem covered_1 : Covered 1 [0] := covered_one
theorem covered_2 : Covered 2 GraphClosure1_000.targets :=
  covered_step 0 [0] GraphClosure1_000.targets covered_1 catalogue_closed_1
theorem covered_3 : Covered 3 GraphClosure2_000.targets :=
  covered_step 1 GraphClosure1_000.targets GraphClosure2_000.targets covered_2 catalogue_closed_2
theorem covered_4 : Covered 4 GraphClosure3_000.targets :=
  covered_step 2 GraphClosure2_000.targets GraphClosure3_000.targets covered_3 catalogue_closed_3
theorem covered_5 : Covered 5 GraphClosure4_000.targets :=
  covered_step 3 GraphClosure3_000.targets GraphClosure4_000.targets covered_4 catalogue_closed_4
theorem covered_6 : Covered 6 GraphClosure5_000.targets :=
  covered_step 4 GraphClosure4_000.targets GraphClosure5_000.targets covered_5 catalogue_closed_5
theorem covered_7 : Covered 7 GraphClosure6_000.targets :=
  covered_step 5 GraphClosure5_000.targets GraphClosure6_000.targets covered_6 catalogue_closed_6
theorem covered_8 : Covered 8 GraphClosure7_000.targets :=
  covered_step 6 GraphClosure6_000.targets GraphClosure7_000.targets covered_7 catalogue_closed_7
theorem coverage8 : Coverage8 := by
  intro C s h
  obtain ⟨code, hc, e, he⟩ := covered_8 (supportGraph C s h)
    (supportGraph_connected C s h) (by
      intro i
      convert supportGraph_degree_le C s h i using 1
      congr 1
      exact Subsingleton.elim _ _)
  refine ⟨e, code, hc, ?_⟩
  intro i j hij
  have hne : e i ≠ e j := fun heq => hij (e.injective heq)
  have hadj : (supportGraph C s h).Adj (e i) (e j) ↔ C (e i) (e j) ≠ 0 :=
    and_iff_right hne
  exact hadj.symm.trans (he i j)
end Nut8
