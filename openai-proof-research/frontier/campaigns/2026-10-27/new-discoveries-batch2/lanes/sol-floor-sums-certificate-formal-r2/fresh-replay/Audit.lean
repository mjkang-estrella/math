import generated.th_lemma_0
import generated.th_lemma_1
import generated.th_lemma_10
import generated.th_lemma_11
import generated.th_lemma_12
import generated.th_lemma_13
import generated.th_lemma_14
import generated.th_lemma_15
import generated.th_lemma_16
import generated.th_lemma_17
import generated.th_lemma_18
import generated.th_lemma_19
import generated.th_lemma_2
import generated.th_lemma_20
import generated.th_lemma_21
import generated.th_lemma_22
import generated.th_lemma_23
import generated.th_lemma_24
import generated.th_lemma_25
import generated.th_lemma_26
import generated.th_lemma_27
import generated.th_lemma_28
import generated.th_lemma_29
import generated.th_lemma_3
import generated.th_lemma_30
import generated.th_lemma_31
import generated.th_lemma_32
import generated.th_lemma_33
import generated.th_lemma_34
import generated.th_lemma_35
import generated.th_lemma_36
import generated.th_lemma_37
import generated.th_lemma_4
import generated.th_lemma_5
import generated.th_lemma_6
import generated.th_lemma_7
import generated.th_lemma_8
import generated.th_lemma_9
import Source
import Expansion
import Lean
set_option autoImplicit false
set_option warningAsError true
set_option pp.all true
set_option pp.maxSteps 10000000
set_option pp.deepTerms true
set_option format.width 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some i => if ["Reduction", "Symmetry", "Source", "Expansion", "generated.th_lemma_0", "generated.th_lemma_1", "generated.th_lemma_10", "generated.th_lemma_11", "generated.th_lemma_12", "generated.th_lemma_13", "generated.th_lemma_14", "generated.th_lemma_15", "generated.th_lemma_16", "generated.th_lemma_17", "generated.th_lemma_18", "generated.th_lemma_19", "generated.th_lemma_2", "generated.th_lemma_20", "generated.th_lemma_21", "generated.th_lemma_22", "generated.th_lemma_23", "generated.th_lemma_24", "generated.th_lemma_25", "generated.th_lemma_26", "generated.th_lemma_27", "generated.th_lemma_28", "generated.th_lemma_29", "generated.th_lemma_3", "generated.th_lemma_30", "generated.th_lemma_31", "generated.th_lemma_32", "generated.th_lemma_33", "generated.th_lemma_34", "generated.th_lemma_35", "generated.th_lemma_36", "generated.th_lemma_37", "generated.th_lemma_4", "generated.th_lemma_5", "generated.th_lemma_6", "generated.th_lemma_7", "generated.th_lemma_8", "generated.th_lemma_9", "Audit"].contains env.header.moduleNames[i]!.toString then some n else none
    | none => none
  for n in names.mergeSort (fun a b => a.toString ≤ b.toString) do
    let some info := env.find? n | throwError "missing declaration"
    let origin := env.header.moduleNames[(env.getModuleIdxFor? n).get!]!
    logInfo m!"DECL|{n}|ORIGIN|{origin}|UNSAFE|{info.isUnsafe}"
    match info with
    | .defnInfo d => logInfo m!"SAFETY|{n}|{repr d.safety}"
    | _ => logInfo m!"SAFETY|{n}|nondefinition"
    elabCommand (← `(#check $(mkIdent n)))
    elabCommand (← `(#print axioms $(mkIdent n)))
