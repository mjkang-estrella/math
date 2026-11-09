import GraphChecker
namespace Nut8.GraphClosure1_000
def targets : List Nat := [6]
def certificates0 : List (Nat × Nat × List Nat) := [
(1, 6, [0, 1])
]
theorem closed0 : extensionClosed 1 0 targets certificates0 = true := by
  decide +kernel
end Nut8.GraphClosure1_000
