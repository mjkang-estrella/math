import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH16_p (x : Points 5) : Points 5 := ([0, 23, 14, 7, 27, 5, 13, 24, 2, 28, 10, 3, 9, 22, 26, 15, 18, 19, 17, 30, 20, 8, 4, 12, 29, 25, 21, 6, 1, 11, 16] : List (Points 5)).getD x.val 0
def CollH16_pi (x : Points 5) : Points 5 := ([0, 28, 8, 11, 22, 5, 27, 3, 21, 12, 10, 29, 23, 6, 2, 15, 30, 18, 16, 17, 20, 26, 13, 1, 7, 25, 14, 4, 9, 24, 19] : List (Points 5)).getD x.val 0
def CollH16_l (x : Points 5) : Points 5 := ([4, 0, 1, 2, 3, 6, 7, 8, 9, 5, 13, 14, 10, 11, 12, 15, 16, 17, 18, 19, 22, 23, 24, 20, 21, 27, 28, 29, 25, 26, 30] : List (Points 5)).getD x.val 0
def CollH16_li (x : Points 5) : Points 5 := ([1, 2, 3, 4, 0, 9, 5, 6, 7, 8, 12, 13, 14, 10, 11, 15, 16, 17, 18, 19, 23, 24, 20, 21, 22, 28, 29, 25, 26, 27, 30] : List (Points 5)).getD x.val 0
def CollH16 : Collineation5 where
  p := CollH16_p
  pinv := CollH16_pi
  l := CollH16_l
  linv := CollH16_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
