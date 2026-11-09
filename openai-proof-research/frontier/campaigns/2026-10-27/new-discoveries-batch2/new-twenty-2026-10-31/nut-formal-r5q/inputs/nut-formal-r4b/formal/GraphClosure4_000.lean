import GraphChecker
namespace Nut8.GraphClosure4_000
def targets : List Nat := [12198416, 5464336, 14377232, 7562000, 14379408, 15256200, 7594776, 3320472, 12233368, 7596952]
def certificates0 : List (Nat × Nat × List Nat) := [
(1, 12198416, [1, 2, 4, 0, 3]),
(2, 12198416, [0, 2, 4, 1, 3]),
(4, 12198416, [0, 1, 4, 2, 3]),
(3, 7562000, [2, 0, 1, 4, 3]),
(5, 7562000, [1, 0, 2, 4, 3]),
(6, 7562000, [0, 1, 2, 4, 3]),
(7, 7594776, [0, 1, 2, 3, 4])
]
theorem closed0 : extensionClosed 4 30856 targets certificates0 = true := by
  decide +kernel
def certificates1 : List (Nat × Nat × List Nat) := [
(1, 5464336, [1, 4, 3, 0, 2]),
(2, 5464336, [0, 4, 2, 1, 3]),
(4, 12198416, [1, 4, 0, 3, 2]),
(8, 12198416, [0, 4, 1, 2, 3]),
(3, 3320472, [0, 1, 2, 3, 4]),
(5, 7562000, [1, 3, 4, 0, 2]),
(9, 15256200, [1, 0, 4, 2, 3]),
(6, 15256200, [0, 1, 4, 3, 2]),
(10, 7562000, [0, 2, 4, 1, 3]),
(12, 14377232, [0, 1, 4, 2, 3]),
(7, 12233368, [1, 0, 3, 2, 4]),
(11, 12233368, [0, 1, 2, 3, 4]),
(13, 14379408, [1, 0, 3, 4, 2]),
(14, 14379408, [0, 1, 2, 4, 3])
]
theorem closed1 : extensionClosed 4 23112 targets certificates1 = true := by
  decide +kernel
def certificates2 : List (Nat × Nat × List Nat) := [
(1, 15256200, [4, 1, 2, 0, 3]),
(2, 14377232, [0, 4, 2, 1, 3]),
(4, 14377232, [0, 4, 1, 2, 3]),
(3, 12233368, [2, 0, 4, 1, 3]),
(5, 12233368, [1, 0, 4, 2, 3]),
(6, 14379408, [0, 4, 1, 2, 3]),
(7, 7596952, [0, 1, 2, 3, 4])
]
theorem closed2 : extensionClosed 4 31432 targets certificates2 = true := by
  decide +kernel
def certificates3 : List (Nat × Nat × List Nat) := [
(1, 7562000, [4, 2, 3, 1, 0]),
(2, 7562000, [4, 2, 3, 0, 1]),
(4, 7562000, [4, 0, 1, 3, 2]),
(8, 7562000, [4, 0, 1, 2, 3]),
(3, 7594776, [2, 3, 4, 0, 1]),
(5, 12233368, [4, 1, 3, 0, 2]),
(9, 12233368, [4, 1, 2, 0, 3]),
(6, 12233368, [4, 0, 3, 1, 2]),
(10, 12233368, [4, 0, 2, 1, 3]),
(12, 7594776, [0, 1, 4, 2, 3]),
(7, 7596952, [3, 2, 4, 0, 1]),
(11, 7596952, [2, 3, 4, 0, 1]),
(13, 7596952, [1, 0, 4, 2, 3]),
(14, 7596952, [0, 1, 4, 2, 3])
]
theorem closed3 : extensionClosed 4 13260 targets certificates3 = true := by
  decide +kernel
def certificates4 : List (Nat × Nat × List Nat) := [
(1, 14379408, [4, 1, 2, 3, 0]),
(2, 14379408, [4, 0, 2, 3, 1]),
(3, 7596952, [4, 2, 3, 0, 1])
]
theorem closed4 : extensionClosed 4 31692 targets certificates4 = true := by
  decide +kernel
def certificates5 : List (Nat × Nat × List Nat) := [

]
theorem closed5 : extensionClosed 4 31710 targets certificates5 = true := by
  decide +kernel
end Nut8.GraphClosure4_000
