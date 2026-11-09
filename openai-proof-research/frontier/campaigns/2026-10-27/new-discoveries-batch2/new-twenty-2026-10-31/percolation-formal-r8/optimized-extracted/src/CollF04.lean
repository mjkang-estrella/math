import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF04_p (x : Points 5) : Points 5 := ([4, 17, 23, 11, 26, 2, 13, 16, 28, 24, 3, 21, 27, 19, 12, 1, 29, 14, 22, 18, 30, 9, 7, 8, 6, 0, 15, 20, 10, 25, 5] : List (Points 5)).getD x.val 0
def CollF04_pi (x : Points 5) : Points 5 := ([25, 15, 5, 10, 0, 30, 24, 22, 23, 21, 28, 3, 14, 6, 17, 26, 7, 1, 19, 13, 27, 11, 18, 2, 9, 29, 4, 12, 8, 16, 20] : List (Points 5)).getD x.val 0
def CollF04_l (x : Points 5) : Points 5 := ([30, 29, 27, 28, 26, 20, 0, 5, 10, 15, 23, 13, 3, 18, 8, 24, 9, 19, 4, 14, 22, 17, 12, 7, 2, 21, 1, 6, 11, 16, 25] : List (Points 5)).getD x.val 0
def CollF04_li (x : Points 5) : Points 5 := ([6, 26, 24, 12, 18, 7, 27, 23, 14, 16, 8, 28, 22, 11, 19, 9, 29, 21, 13, 17, 5, 25, 20, 10, 15, 30, 4, 2, 3, 1, 0] : List (Points 5)).getD x.val 0
def CollF04 : Collineation5 where
  p := CollF04_p
  pinv := CollF04_pi
  l := CollF04_l
  linv := CollF04_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
