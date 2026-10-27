import SourceAssembly
import MomentOpen

namespace RepeatedIntegrals

theorem source_moment_image (n : ℕ) :
    SourceW n = endpointMomentTransform n '' smoothMomentSet n :=
  sourceW_eq_smoothMomentImage n (smoothMomentSet_convex n) (smoothMomentSet_isOpen n)

theorem source_conjecture_371768 : SourceConjecture371768 :=
  source_conjecture_of_moment_openness smoothMomentSet_convex smoothMomentSet_isOpen

end RepeatedIntegrals
