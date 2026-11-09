import CMDRRNormalize
import CMDRRRepeat
import CMDRRSwap
import Lean.Util.CollectAxioms

open Lean Elab Command

elab "audit_production" : command => do
  let env ← getEnv
  let roots := #[``CMDRR.Game, ``CMDRR.Game.display, ``CMDRR.Game.other,
    ``CMDRR.Game.relabel, ``CMDRR.Source.relabel, ``CMDRR.Source.U,
    ``CMDRR.cells_card, ``CMDRR.Source.row_twoCycle_single,
    ``CMDRR.Source.swap, ``CMDRR.Matching.normalized_labels]
  let mut total : Nat := 0
  for (n,ci) in env.constants.toList do
    if roots.any (fun r => env.getModuleIdxFor? r == env.getModuleIdxFor? n) then
      total := total + 1
      let axs ← Lean.collectAxioms n
      let deps := ci.type.getUsedConstants ++
        (ci.value? (allowOpaque := true)).toArray.flatMap Expr.getUsedConstants
      logInfo m!"DECL {n} AXIOMS {axs} DIRECT_DEPS {deps}"
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "disallowed axiom {ax} in {n}"
  logInfo m!"PRODUCTION_DECLARATION_COUNT {total}"

audit_production
#print CMDRR.Source
#print CMDRR.ExistsFiveThree
#print axioms CMDRR.Source.games_eleven
#print axioms CMDRR.Matching.normalized_labels
#print axioms CMDRR.Source.row_twoCycle_single
#print axioms CMDRR.Source.C_T
