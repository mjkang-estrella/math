import GraphChecker
namespace Nut8.GraphClosure3_000
def targets : List Nat := [30856, 23112, 31432, 13260, 31692, 31710]
def certificates0 : List (Nat × Nat × List Nat) := [
(1, 23112, [1, 3, 0, 2]),
(2, 23112, [0, 3, 1, 2]),
(4, 30856, [0, 1, 3, 2]),
(3, 13260, [0, 1, 2, 3]),
(5, 31432, [1, 0, 3, 2]),
(6, 31432, [0, 1, 3, 2]),
(7, 31692, [0, 1, 2, 3])
]
theorem closed0 : extensionClosed 3 228 targets certificates0 = true := by
  decide +kernel
def certificates1 : List (Nat × Nat × List Nat) := [
(1, 31432, [3, 1, 2, 0]),
(2, 31432, [3, 0, 2, 1]),
(4, 31432, [3, 0, 1, 2]),
(3, 31692, [2, 3, 0, 1]),
(5, 31692, [1, 3, 0, 2]),
(6, 31692, [0, 3, 1, 2]),
(7, 31710, [0, 1, 2, 3])
]
theorem closed1 : extensionClosed 3 238 targets certificates1 = true := by
  decide +kernel
end Nut8.GraphClosure3_000
