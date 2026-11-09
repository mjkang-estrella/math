import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG18_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 24, 8, 10, 27, 17, 12, 23, 28, 9, 15, 6, 25, 21, 11, 16, 26, 13, 7, 20, 19, 18, 22, 5, 14, 29, 1] : List (Points 5)).getD x.val 0
def CollG18_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 27, 15, 22, 6, 13, 7, 18, 10, 21, 28, 14, 19, 9, 25, 24, 23, 17, 26, 11, 5, 16, 20, 8, 12, 29, 4] : List (Points 5)).getD x.val 0
def CollG18_l (x : Points 5) : Points 5 := ([24, 15, 11, 7, 3, 9, 0, 21, 17, 13, 19, 10, 6, 2, 23, 4, 20, 16, 12, 8, 14, 5, 1, 22, 18, 25, 26, 30, 27, 28, 29] : List (Points 5)).getD x.val 0
def CollG18_li (x : Points 5) : Points 5 := ([6, 22, 13, 4, 15, 21, 12, 3, 19, 5, 11, 2, 18, 9, 20, 1, 17, 8, 24, 10, 16, 7, 23, 14, 0, 25, 26, 28, 29, 30, 27] : List (Points 5)).getD x.val 0
def CollG18 : Collineation5 where
  p := CollG18_p
  pinv := CollG18_pi
  l := CollG18_l
  linv := CollG18_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
