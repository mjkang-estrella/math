import GraphChecker
namespace Nut8.GraphClosure2_000
def targets : List Nat := [228, 238]
def certificates0 : List (Nat × Nat × List Nat) := [
(1, 228, [1, 2, 0]),
(2, 228, [0, 2, 1]),
(3, 238, [0, 1, 2])
]
theorem closed0 : extensionClosed 2 6 targets certificates0 = true := by
  decide +kernel
end Nut8.GraphClosure2_000
