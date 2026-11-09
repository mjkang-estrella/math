import Nut
import GlobalLabel
import Character
import CubicCancellation
import SignedQuotient
import GraphCoordinates
import KernelLift
import QuotientExtraction
import FullCofactor
import VerifiedDet
import FiniteGrammar
import MatrixExtraction
import NutConnected
import AdmissibleCounting
import AdmissibleDiagonal
import CertificateBench
import DetPilot
import HardDet
import HardCofactor
import Audit
import Invariances
import TreeSwitch
import GraphChecker
import GraphExtensions2_000
import GraphExtensions3_000
import GraphExtensions4_000
import GraphExtensions5_000
import GraphExtensions6_000
import GraphExtensions6_001
import GraphExtensions7_000
import GraphExtensions7_001
import GraphExtensions7_002
import GraphExtensions7_003
import GraphExtensions8_000
import GraphExtensions8_001
import GraphExtensions8_002
import GraphExtensions8_003
import GraphExtensions8_004
import GraphExtensions8_005
import GraphExtensions8_006
import GraphExtensions8_007
import GraphExtensions8_008
import GraphExtensions8_009
import GraphExtensions8_010
import GraphExtensions8_011
import GraphClosure1_000
import GraphClosure2_000
import GraphClosure3_000
import GraphClosure4_000
import GraphClosure5_000
import GraphClosure5_001
import GraphClosure6_000
import GraphClosure6_001
import GraphClosure6_002
import GraphClosure6_003
import GraphClosure7_000
import GraphClosure7_001
import GraphClosure7_002
import GraphClosure7_003
import GraphClosure7_004
import GraphClosure7_005
import GraphClosure7_006
import GraphClosure7_007
import Certificates0000
import AuditR3
import SupportGraph
import CheckedGraphIso
import GraphDeletion
import AuditR4
import BitEncoding
import CatalogueGraph
import CatalogueSimple1
import CatalogueSimple2
import CatalogueSimple3
import CatalogueSimple4
import CatalogueSimple5
import CatalogueSimple6
import CatalogueSimple7
import CatalogueSimple8
import CyclicBridge
import EndpointOfFinite
import NutInterface
import FiniteOfParts
import EndpointOfParts
import RowEncoding
import ExtensionEncoding
import R3Audit
import SmallOrbitCases
import R4Audit
import TransportedNeighbors
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    if mod.any (fun m => #[`Nut, `GlobalLabel, `Character, `CubicCancellation, `SignedQuotient, `GraphCoordinates, `KernelLift, `QuotientExtraction, `FullCofactor, `VerifiedDet, `FiniteGrammar, `MatrixExtraction, `NutConnected, `AdmissibleCounting, `AdmissibleDiagonal, `CertificateBench, `DetPilot, `HardDet, `HardCofactor, `Audit, `Invariances, `TreeSwitch, `GraphChecker, `GraphExtensions2_000, `GraphExtensions3_000, `GraphExtensions4_000, `GraphExtensions5_000, `GraphExtensions6_000, `GraphExtensions6_001, `GraphExtensions7_000, `GraphExtensions7_001, `GraphExtensions7_002, `GraphExtensions7_003, `GraphExtensions8_000, `GraphExtensions8_001, `GraphExtensions8_002, `GraphExtensions8_003, `GraphExtensions8_004, `GraphExtensions8_005, `GraphExtensions8_006, `GraphExtensions8_007, `GraphExtensions8_008, `GraphExtensions8_009, `GraphExtensions8_010, `GraphExtensions8_011, `GraphClosure1_000, `GraphClosure2_000, `GraphClosure3_000, `GraphClosure4_000, `GraphClosure5_000, `GraphClosure5_001, `GraphClosure6_000, `GraphClosure6_001, `GraphClosure6_002, `GraphClosure6_003, `GraphClosure7_000, `GraphClosure7_001, `GraphClosure7_002, `GraphClosure7_003, `GraphClosure7_004, `GraphClosure7_005, `GraphClosure7_006, `GraphClosure7_007, `Certificates0000, `AuditR3, `SupportGraph, `CheckedGraphIso, `GraphDeletion, `AuditR4, `BitEncoding, `CatalogueGraph, `CatalogueSimple1, `CatalogueSimple2, `CatalogueSimple3, `CatalogueSimple4, `CatalogueSimple5, `CatalogueSimple6, `CatalogueSimple7, `CatalogueSimple8, `CyclicBridge, `EndpointOfFinite, `NutInterface, `FiniteOfParts, `EndpointOfParts, `RowEncoding, `ExtensionEncoding, `R3Audit, `SmallOrbitCases, `R4Audit, `TransportedNeighbors].contains m) then
      count := count + 1
      logInfo m!"MODULE {mod} DECL {n} TYPE {ci.type}"
      logInfo m!"BODY {n} {ci.value? (allowOpaque := true)}"
      logInfo m!"FLAGS unsafe={ci.isUnsafe} partial={ci.isPartial} axiom={ci.isAxiom}"
      if ci.isUnsafe || ci.isPartial || ci.isAxiom then throwError "forbidden declaration {n}"
      let axs ← Lean.collectAxioms n
      logInfo m!"AXIOMS {n} {axs}"
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "forbidden axiom {ax} in {n}"
      elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"LOCAL_TOTAL {count}"
