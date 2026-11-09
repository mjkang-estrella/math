import ShoeColorPMF
import ShoeColorControls
import ShoeSemanticControls
import ShoeAxiomAudit
import ShoeEndpointAxioms
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let all := env.constants.fold (fun (acc : Array Json) n ci => if n.hash % 8 == 2 then acc.push (Json.mkObj [("name", toJson n.toString), ("origin", toJson (match env.getModuleIdxFor? n with | some k => env.header.moduleNames[k]!.toString | none => "CURRENT")), ("unsafe", toJson ci.isUnsafe)]) else acc) #[]
  liftIO <| IO.println ("ENV_METADATA " ++ (Json.arr all).compress)
