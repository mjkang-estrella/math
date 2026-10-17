import Controls
open AGM063 AGMControls
example : (false,true) ∈ ((relationPairs universalPair ∩ (leftPoint ×ˢ leftPoint)) ∪
    (leftPointᶜ ×ˢ leftPointᶜ)) := by
  simp [relationPairs, universalPair, leftPoint]
