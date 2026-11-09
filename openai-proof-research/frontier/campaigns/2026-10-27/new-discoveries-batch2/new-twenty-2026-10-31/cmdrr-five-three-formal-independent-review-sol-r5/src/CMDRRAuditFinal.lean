import CMDRRColumnCycles
import CMDRRControls
import CMDRRNormalizationBridge
import Lean.Util.CollectAxioms

open Lean Elab Command
elab "audit_final" : command => do
  let env ← getEnv
  let roots := #[``CMDRR.Game, ``CMDRR.Game.display, ``CMDRR.Game.other,
    ``CMDRR.Game.relabel, ``CMDRR.Source.relabel, ``CMDRR.Source.U,
    ``CMDRR.cells_card, ``CMDRR.Source.row_twoCycle_single,
    ``CMDRR.Source.swap, ``CMDRR.Matching.normalized_labels,
    ``CMDRR.Source.row_twoCycles_overlap, ``CMDRR.four_orbit,
    ``CMDRR.orbit_four_of_not_two, ``CMDRR.Source.unique_other_man_count,
    ``CMDRR.Source.rowPerm, ``CMDRR.canonical,
    ``CMDRR.Source.canonical_transport, ``CMDRR.complementary_internal_edges,
    ``CMDRR.Source.spouse_row_four, ``CMDRR.Source.row_complementary_degree,
    ``CMDRR.Source.row_twoCycle_games, ``CMDRR.Source.A_zero_of_single_twoCycle, ``CMDRR.Source.female_single_occurrence_partition, ``CMDRR.Source.rowOccurrence, ``CMDRR.Game.spouse_man_incidence, ``CMDRR.count_as_sum, ``CMDRR.Game.married_pair_indicator, ``CMDRR.Source.central_incidence_identity, ``CMDRR.Source.no_single_twoCycle, ``CMDRR.orbit_five_of_no_two, ``CMDRR.canonicalTranspose, ``CMDRR.Source.row_sign, ``CMDRR.Source.U_sign, ``CMDRR.universalExistsFiveThree_negation, ``CMDRR.Source.spouse_column_four, ``CMDRR.Controls.positive_source]
  let mut production : Array Name := #[]
  logInfo m!"WHOLE_ENV_COUNT {env.constants.toList.length}"
  for (n, ci) in env.constants.toList do
    logInfo m!"ENV_DECL {n} ORIGIN {repr ((env.getModuleIdxFor? n).map ModuleIdx.toNat)} HAS_BODY {(ci.value? (allowOpaque := true)).isSome}"
    if roots.any (fun r => env.getModuleIdxFor? r == env.getModuleIdxFor? n) then
      production := production.push n
      let axs ← Lean.collectAxioms n
      logInfo m!"PRODUCTION {n} AXIOMS {axs}"
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "disallowed axiom {ax} in {n}"
  logInfo m!"PRODUCTION_COUNT {production.size}"
  logInfo m!"MODULE_NAMES {repr env.header.moduleNames}"
  let mut todo := production
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        let deps := ci.type.getUsedConstants ++
          (ci.value? (allowOpaque := true)).toArray.flatMap Expr.getUsedConstants
        logInfo m!"BODY_NODE {n} ORIGIN {repr ((env.getModuleIdxFor? n).map ModuleIdx.toNat)} HAS_BODY {(ci.value? (allowOpaque := true)).isSome} DEPS {deps}"
        todo := todo ++ deps
      else
        throwError "missing dependency {n}"
  logInfo m!"BODY_NODE_COUNT {seen.size}"
  for root in #[``CMDRR.Source.spouse_column_four, ``CMDRR.Source.single_column_five, ``CMDRR.Controls.positive_source, ``CMDRR.Source.canonical_transport, ``CMDRR.Source.central_incidence_identity, ``CMDRR.Source.B_add_z_of_single_twoCycle, ``CMDRR.Source.no_single_twoCycle, ``CMDRR.Source.single_row_five, ``CMDRR.Source.swapped_U_is_C, ``CMDRR.Source.U_sign, ``CMDRR.Source.C_sign, ``CMDRR.Source.T_sign, ``CMDRR.canonical_noSource, ``CMDRR.noSource_five_three, ``CMDRR.universalExistsFiveThree_negation] do
    let mut worklist := #[root]
    let mut visited : NameSet := {}
    let mut closure : Array Name := #[]
    while !worklist.isEmpty do
      let n := worklist.back!
      worklist := worklist.pop
      unless visited.contains n do
        visited := visited.insert n
        closure := closure.push n
        if let some ci := env.find? n then
          worklist := worklist ++ ci.type.getUsedConstants ++
            (ci.value? (allowOpaque := true)).toArray.flatMap Expr.getUsedConstants
    logInfo m!"ENDPOINT_CLOSURE {root} {closure}"
    logInfo m!"ENDPOINT_AXIOMS {root} {← Lean.collectAxioms root}"

audit_final
