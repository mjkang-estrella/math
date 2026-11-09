import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF24_p (x : Points 5) : Points 5 := ([24, 10, 17, 8, 27, 12, 15, 9, 28, 23, 18, 5, 29, 22, 14, 6, 25, 21, 11, 16, 26, 20, 13, 19, 7, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF24_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 11, 15, 24, 3, 7, 1, 18, 5, 22, 14, 6, 19, 2, 10, 23, 21, 17, 13, 9, 0, 16, 20, 4, 8, 12, 29] : List (Points 5)).getD x.val 0
def CollF24_l (x : Points 5) : Points 5 := ([25, 27, 26, 28, 30, 9, 0, 21, 17, 13, 24, 7, 15, 3, 11, 4, 16, 8, 20, 12, 19, 23, 2, 6, 10, 14, 5, 1, 22, 18, 29] : List (Points 5)).getD x.val 0
def CollF24_li (x : Points 5) : Points 5 := ([6, 27, 22, 13, 15, 26, 23, 11, 17, 5, 24, 14, 19, 9, 25, 12, 16, 8, 29, 20, 18, 7, 28, 21, 10, 0, 2, 1, 3, 30, 4] : List (Points 5)).getD x.val 0
def CollF24 : Collineation5 where
  p := CollF24_p
  pinv := CollF24_pi
  l := CollF24_l
  linv := CollF24_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
