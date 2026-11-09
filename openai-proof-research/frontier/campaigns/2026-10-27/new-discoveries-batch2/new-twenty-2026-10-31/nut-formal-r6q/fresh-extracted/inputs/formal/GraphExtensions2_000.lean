import GraphChecker
namespace Nut8.GraphExtensions2_000
def data : List (Nat × Nat × List Nat) := [
(6, 6, [0, 1])
]
theorem checked : data.all (fun c => graphIsoCheck 2 c.1 c.2.1 c.2.2) = true := by
  decide +kernel
end Nut8.GraphExtensions2_000
