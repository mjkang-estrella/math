import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH11_p (x : Points 5) : Points 5 := ([0, 8, 19, 22, 28, 5, 23, 4, 17, 26, 10, 13, 14, 12, 30, 15, 3, 24, 7, 29, 20, 18, 9, 2, 27, 25, 16, 1, 21, 6, 11] : List (Points 5)).getD x.val 0
def CollH11_pi (x : Points 5) : Points 5 := ([0, 27, 23, 16, 7, 5, 29, 18, 1, 22, 10, 30, 13, 11, 12, 15, 26, 8, 21, 2, 20, 28, 3, 6, 17, 25, 9, 24, 4, 19, 14] : List (Points 5)).getD x.val 0
def CollH11_l (x : Points 5) : Points 5 := ([4, 0, 1, 2, 3, 7, 8, 9, 5, 6, 10, 11, 12, 13, 14, 18, 19, 15, 16, 17, 21, 22, 23, 24, 20, 28, 29, 25, 26, 27, 30] : List (Points 5)).getD x.val 0
def CollH11_li (x : Points 5) : Points 5 := ([1, 2, 3, 4, 0, 8, 9, 5, 6, 7, 10, 11, 12, 13, 14, 17, 18, 19, 15, 16, 24, 20, 21, 22, 23, 27, 28, 29, 25, 26, 30] : List (Points 5)).getD x.val 0
def CollH11 : Collineation5 where
  p := CollH11_p
  pinv := CollH11_pi
  l := CollH11_l
  linv := CollH11_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
