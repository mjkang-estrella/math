import MaskRUP
import MaskPilot0000
import MaskPilot0100
import MaskPilot0200
import MaskPilot0300
import MaskPilot0400
import MaskPilot0500
import MaskPilot0600
import MaskPilot0700
import MaskPilot0800
import MaskPilot0900
import MaskBuild
import MaskRaw0000
import MaskRaw0100
import MaskRaw0200
import MaskRaw0300
import MaskRaw0400
import MaskRaw0500
import MaskRaw0600
import MaskRaw0700
import MaskRaw0800
import MaskRaw0900
import MaskRaw1000
import MaskRaw1100
import MaskRaw1200
import MaskRaw1300
import MaskRaw1400
import MaskRaw1500
import MaskRaw1600
import MaskRaw1700
import MaskRaw1800
import MaskRaw1900
import MaskRaw2000
import MaskRaw2100
import MaskRaw2200
import MaskRaw2300
import MaskRaw2400
import MaskRaw2500
import MaskRaw2600
import MaskRaw2700
import MaskRaw2800
import MaskRaw2900
import MaskRaw3000
import MaskRaw3100
import MaskRaw3200
import MaskRaw3300
import MaskRaw3400
import MaskRaw3500
import MaskRaw3600
import MaskRaw3700
import MaskRaw3800
import MaskRaw3900
import MaskRaw4000
import MaskRaw4100
import MaskRaw4200
import MaskRaw4300
import MaskRaw4400
import MaskRaw4500
import MaskRaw4600
import MaskRaw4700
import MaskRaw4800
import MaskRaw4900
import Definitions
import Plane5
import ControlBase
import Sep4_2
import Sep4_6
import Sep4_8
import Sep4_11
import Sep4_12
import Sep4_16
import Sep4_18
import Sep4_20
import Sep4_21
import Sep4_26
import Sep5_0
import Sep5_3
import Sep5_4
import Sep5_6
import Sep5_7
import Sep5_9
import Sep5_10
import Sep5_12
import Sep5_13
import Sep5_17
import Sep5_18
import Sep5_21
import Sep5_22
import Sep5_25
import Sep5_26
import Sep5_27
import Control4
import Control5
import Structure
import Endpoint
import Closure
import FiniteSystem
import TruthTableCNF
import PG5CNF
import RUP
import InputLink
import Collineation
import CollF00
import CollF01
import CollF02
import CollF03
import CollF04
import CollF05
import CollF06
import CollF07
import CollF08
import CollF09
import CollF10
import CollF11
import CollF12
import CollF13
import CollF14
import CollF15
import CollF16
import CollF17
import CollF18
import CollF19
import CollF20
import CollF21
import CollF22
import CollF23
import CollF24
import CollF25
import CollF26
import CollF27
import CollF28
import CollF29
import CollF30
import CollG01
import CollG02
import CollG03
import CollG04
import CollG05
import CollG06
import CollG07
import CollG08
import CollG09
import CollG10
import CollG11
import CollG12
import CollG13
import CollG14
import CollG15
import CollG16
import CollG17
import CollG18
import CollG19
import CollG20
import CollG21
import CollG22
import CollG23
import CollG24
import CollG25
import CollG26
import CollG27
import CollG28
import CollG29
import CollG30
import CollH01
import CollH02
import CollH03
import CollH04
import CollH06
import CollH07
import CollH08
import CollH09
import CollH11
import CollH12
import CollH13
import CollH14
import CollH16
import CollH17
import CollH18
import CollH19
import CollH21
import CollH22
import CollH23
import CollH24
import CollH26
import CollH27
import CollH28
import CollH29
import CollH30
import CollineationFamily
import Noncollinear
import Normalize
import NormalizedExport
import MaskCNF
import EndpointR6
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let localModules : Array String := #["MaskRUP","MaskPilot0000","MaskPilot0100","MaskPilot0200","MaskPilot0300","MaskPilot0400","MaskPilot0500","MaskPilot0600","MaskPilot0700","MaskPilot0800","MaskPilot0900","MaskBuild","MaskRaw0000","MaskRaw0100","MaskRaw0200","MaskRaw0300","MaskRaw0400","MaskRaw0500","MaskRaw0600","MaskRaw0700","MaskRaw0800","MaskRaw0900","MaskRaw1000","MaskRaw1100","MaskRaw1200","MaskRaw1300","MaskRaw1400","MaskRaw1500","MaskRaw1600","MaskRaw1700","MaskRaw1800","MaskRaw1900","MaskRaw2000","MaskRaw2100","MaskRaw2200","MaskRaw2300","MaskRaw2400","MaskRaw2500","MaskRaw2600","MaskRaw2700","MaskRaw2800","MaskRaw2900","MaskRaw3000","MaskRaw3100","MaskRaw3200","MaskRaw3300","MaskRaw3400","MaskRaw3500","MaskRaw3600","MaskRaw3700","MaskRaw3800","MaskRaw3900","MaskRaw4000","MaskRaw4100","MaskRaw4200","MaskRaw4300","MaskRaw4400","MaskRaw4500","MaskRaw4600","MaskRaw4700","MaskRaw4800","MaskRaw4900","Definitions","Plane5","ControlBase","Sep4_2","Sep4_6","Sep4_8","Sep4_11","Sep4_12","Sep4_16","Sep4_18","Sep4_20","Sep4_21","Sep4_26","Sep5_0","Sep5_3","Sep5_4","Sep5_6","Sep5_7","Sep5_9","Sep5_10","Sep5_12","Sep5_13","Sep5_17","Sep5_18","Sep5_21","Sep5_22","Sep5_25","Sep5_26","Sep5_27","Control4","Control5","Structure","Endpoint","Closure","FiniteSystem","TruthTableCNF","PG5CNF","RUP","InputLink","Collineation","CollF00","CollF01","CollF02","CollF03","CollF04","CollF05","CollF06","CollF07","CollF08","CollF09","CollF10","CollF11","CollF12","CollF13","CollF14","CollF15","CollF16","CollF17","CollF18","CollF19","CollF20","CollF21","CollF22","CollF23","CollF24","CollF25","CollF26","CollF27","CollF28","CollF29","CollF30","CollG01","CollG02","CollG03","CollG04","CollG05","CollG06","CollG07","CollG08","CollG09","CollG10","CollG11","CollG12","CollG13","CollG14","CollG15","CollG16","CollG17","CollG18","CollG19","CollG20","CollG21","CollG22","CollG23","CollG24","CollG25","CollG26","CollG27","CollG28","CollG29","CollG30","CollH01","CollH02","CollH03","CollH04","CollH06","CollH07","CollH08","CollH09","CollH11","CollH12","CollH13","CollH14","CollH16","CollH17","CollH18","CollH19","CollH21","CollH22","CollH23","CollH24","CollH26","CollH27","CollH28","CollH29","CollH30","CollineationFamily","Noncollinear","Normalize","NormalizedExport","MaskCNF","EndpointR6","AuditR6"]
  for m in localModules do
    if m != "AuditR6" && !(env.header.moduleNames.any (fun n => n.toString == m)) then
      throwError "Missing local module from audit: {m}"
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "AuditR6"
    if localModules.contains owner then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden local metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local assumption: {n}"
      | _ => pure ()
  logInfo m!"Metadata audit passed: {count} declarations"

#print axioms Percolation.MaskRUP.rawSound18560
