import CatalogueTrees000
import CatalogueTrees001
import CatalogueTrees002
import CatalogueTrees003
import CatalogueTrees004
import CatalogueTrees005
import CatalogueTrees006
import CatalogueTrees007
import CatalogueTrees008
import CatalogueTrees009
import CatalogueTrees010
import CatalogueTrees011
import CatalogueTrees012
import CatalogueTrees013
import CatalogueTrees014
import CatalogueTrees015
import CatalogueTrees016
import CatalogueTrees017
import CatalogueTrees018
import CatalogueTrees019
namespace Nut8
def catalogueTreeRecords : List (Nat × List Nat × List Nat) :=
  CatalogueTrees000.records ++ CatalogueTrees001.records ++ CatalogueTrees002.records ++ CatalogueTrees003.records ++ CatalogueTrees004.records ++ CatalogueTrees005.records ++ CatalogueTrees006.records ++ CatalogueTrees007.records ++ CatalogueTrees008.records ++ CatalogueTrees009.records ++ CatalogueTrees010.records ++ CatalogueTrees011.records ++ CatalogueTrees012.records ++ CatalogueTrees013.records ++ CatalogueTrees014.records ++ CatalogueTrees015.records ++ CatalogueTrees016.records ++ CatalogueTrees017.records ++ CatalogueTrees018.records ++ CatalogueTrees019.records
theorem catalogueTreeCodes : catalogueTreeRecords.map Prod.fst = GraphClosure7_000.targets := by
  decide +kernel
theorem catalogueTrees_checked : catalogueTreeRecords.all (fun r => orderedTreeCheck r.1 r.2.1 r.2.2) = true := by
  simp only [catalogueTreeRecords, List.all_append]
  simp only [CatalogueTrees000.checked, CatalogueTrees001.checked, CatalogueTrees002.checked, CatalogueTrees003.checked, CatalogueTrees004.checked, CatalogueTrees005.checked, CatalogueTrees006.checked, CatalogueTrees007.checked, CatalogueTrees008.checked, CatalogueTrees009.checked, CatalogueTrees010.checked, CatalogueTrees011.checked, CatalogueTrees012.checked, CatalogueTrees013.checked, CatalogueTrees014.checked, CatalogueTrees015.checked, CatalogueTrees016.checked, CatalogueTrees017.checked, CatalogueTrees018.checked, CatalogueTrees019.checked, Bool.and_self]
end Nut8
namespace Nut8

theorem catalogue_ordered_tree (code : Nat) (hc : code ∈ GraphClosure7_000.targets) :
    ∃ e : Equiv.Perm (Fin 8), ∃ p : Fin 8 → Fin 8,
      ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧
        graphBit 8 code (e (p i)).val (e i).val = true := by
  have hm : code ∈ catalogueTreeRecords.map Prod.fst := by rwa [catalogueTreeCodes]
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
  subst code
  exact orderedTreeCheck_sound r.1 r.2.1 r.2.2
    (List.all_eq_true.mp catalogueTrees_checked r hr)
end Nut8
