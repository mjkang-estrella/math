import GraphChecker
namespace Nut8.GraphExtensions3_000
def data : List (Nat × Nat × List Nat) := [
(78, 228, [1, 2, 0]),
(170, 228, [0, 2, 1]),
(238, 238, [0, 1, 2])
]
theorem checked : data.all (fun c => graphIsoCheck 3 c.1 c.2.1 c.2.2) = true := by
  decide +kernel
end Nut8.GraphExtensions3_000
