import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF16_p (x : Points 5) : Points 5 := ([16, 21, 6, 11, 25, 23, 9, 12, 28, 15, 7, 13, 26, 19, 20, 14, 29, 18, 22, 5, 27, 17, 24, 8, 10, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF16_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 19, 2, 10, 23, 6, 24, 3, 7, 11, 15, 9, 0, 21, 17, 13, 14, 1, 18, 5, 22, 4, 12, 20, 8, 16, 29] : List (Points 5)).getD x.val 0
def CollF16_l (x : Points 5) : Points 5 := ([25, 30, 29, 28, 26, 14, 0, 16, 7, 23, 9, 2, 20, 18, 11, 24, 1, 8, 10, 17, 19, 3, 12, 21, 5, 4, 15, 6, 22, 13, 27] : List (Points 5)).getD x.val 0
def CollF16_li (x : Points 5) : Points 5 := ([6, 16, 11, 21, 25, 24, 27, 8, 17, 10, 18, 14, 22, 29, 5, 26, 7, 19, 13, 20, 12, 23, 28, 9, 15, 0, 4, 30, 3, 2, 1] : List (Points 5)).getD x.val 0
def CollF16 : Collineation5 where
  p := CollF16_p
  pinv := CollF16_pi
  l := CollF16_l
  linv := CollF16_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
