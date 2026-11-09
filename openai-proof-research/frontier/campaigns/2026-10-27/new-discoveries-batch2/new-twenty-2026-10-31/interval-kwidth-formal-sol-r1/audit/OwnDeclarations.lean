import IntervalControls
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if name.toString.startsWith "IntervalWidth." || name.toString.startsWith "_private.Interval" then
      let axioms ← Lean.collectAxioms name
      logInfo m!"AUDIT {name}: unsafe={ci.isUnsafe}; axioms={axioms}; origin={env.getModuleIdxFor? name}; type={ci.type}; body={ci.value? true}"
