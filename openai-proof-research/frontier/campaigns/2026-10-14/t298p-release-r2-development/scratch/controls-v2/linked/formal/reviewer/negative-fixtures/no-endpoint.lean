import Mathlib.Tactic
namespace T298P
theorem gap_transfer (c eMicro eStar micro0 micro1 star0 star1
    sourceMicro0 sourceMicro1 sourceStar0 sourceStar1 : ℝ)
    (_hc : 0 ≤ c) (_hm : 0 ≤ eMicro) (_hs : 0 ≤ eStar)
    
    (lower : c * (sourceMicro1 - sourceMicro0) - eMicro ≤ micro1 - micro0)
    (upper : star1 - star0 ≤ c * (sourceStar1 - sourceStar0) + eStar) :
    c * ((sourceStar0 - sourceMicro0) - (sourceStar1 - sourceMicro1))
      - (eMicro + eStar) ≤ star0 - micro0 := by
  linarith

end T298P
