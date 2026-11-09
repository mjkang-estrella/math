import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG24_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 12, 15, 9, 28, 23, 6, 11, 25, 16, 21, 18, 29, 14, 5, 22, 26, 7, 19, 13, 20, 24, 10, 17, 8, 27, 1] : List (Points 5)).getD x.val 0
def CollG24_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 18, 10, 21, 28, 7, 26, 11, 5, 23, 17, 6, 13, 27, 15, 22, 24, 14, 19, 9, 25, 12, 20, 29, 8, 16, 4] : List (Points 5)).getD x.val 0
def CollG24_l (x : Points 5) : Points 5 := ([14, 5, 1, 22, 18, 9, 0, 21, 17, 13, 4, 20, 16, 12, 8, 24, 15, 11, 7, 3, 19, 10, 6, 2, 23, 25, 27, 26, 28, 30, 29] : List (Points 5)).getD x.val 0
def CollG24_li (x : Points 5) : Points 5 := ([6, 2, 23, 19, 10, 1, 22, 18, 14, 5, 21, 17, 13, 9, 0, 16, 12, 8, 4, 20, 11, 7, 3, 24, 15, 25, 27, 26, 28, 30, 29] : List (Points 5)).getD x.val 0
def CollG24 : Collineation5 where
  p := CollG24_p
  pinv := CollG24_pi
  l := CollG24_l
  linv := CollG24_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
