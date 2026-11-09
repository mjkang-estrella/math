import OrderedTreeCheck
namespace Nut8.CatalogueTrees019
def records : List (Nat × List Nat × List Nat) := [
(942972407950360962, [0, 1, 7, 6, 2, 3, 4, 5], [0, 0, 0, 1, 2, 2, 3, 4]),
(950906363594162562, [0, 1, 7, 6, 2, 3, 4, 5], [0, 0, 0, 1, 2, 2, 3, 3]),
(5010848512597836162, [0, 1, 7, 6, 2, 3, 4, 5], [0, 0, 0, 1, 2, 3, 4, 4]),
(950915279475982722, [0, 1, 7, 6, 2, 3, 4, 5], [0, 0, 0, 1, 2, 2, 3, 3])
]
theorem checked : records.all (fun r => orderedTreeCheck r.1 r.2.1 r.2.2) = true := by
  decide +kernel
end Nut8.CatalogueTrees019
