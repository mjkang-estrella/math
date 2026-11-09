import Data27
import Controls
import Enumeration
import MaskSemantics
import LowerIndexed
import Tree28_000
import Tree28_001
import Tree28_002
import Tree28_003
import Tree28_004
import Tree28_005
import Tree28_006
import Tree28_007
import Tree28_008
import Tree28_009
import Tree28_010
import Tree28_011
import Tree28_012
import Tree28_013
import Tree28_014
import Tree28_015
import Tree28_016
import Tree28_017
import Tree28_018
import Tree28_019
import Tree28_020
import Tree28_021
import Tree28_022
import Tree28_023
import Tree28_024
import Tree28_025
import Tree28_026
import Tree28_027
import Tree28_028
import Tree28_029
import Tree28_030
import Tree28_031
import Tree28_032
import Tree28_033
import Tree28_034
import Tree28_035
import Tree28_036
import Tree28_037
import Tree28_038
import Tree28_039
import Tree28_040
import Tree28_041
import Tree28_042
import Tree28_043
import Tree28_044
import Tree28_045
import Tree28_046
import Tree28_047
import Tree28_048
import Tree28_049
import Tree28_050
import Tree28_051
import Tree28_052
import Tree28_053
import Tree28_054
import Tree28_055
import Tree28_056
import Tree28_057
import Tree28_058
import Tree28_059
import Tree28_060
import Tree28_061
import Tree28_062
import Tree28_063
import Tree28_064
import Tree28_065
import Tree28_066
import Tree28_067
import Tree28_068
import Tree28_069
import Tree28_070
import Tree28_071
import Tree28_072
import Tree28_073
import Tree28_074
import Tree28_075
import Tree28_076
import Tree28_077
import Tree28_078
import Tree28_079
import Tree28_080
import Tree28_081
import Tree28_082
import Tree28_083
import Tree28_084
import Tree28_085
import Tree28_086
import Tree28_087
import Tree28_088
import Tree28_089
import Tree28_090
import Tree28_091
import Tree28_092
import Tree28_093
import Tree28_094
import Tree28_095
import Tree28_096
import Tree28_097
import Tree28_098
import Tree28_099
import Tree28_100
import Tree28_101
import Tree28_102
import Tree28_103
import Tree28_104
import Tree28_105
import Tree28_106
import Tree28_107
import Tree28_108
import Tree28_109
import Tree28_110
import Tree28_111
import Tree28_112
import Tree28_113
import Tree28_114
import Tree28_115

import Lean.Util.CollectAxioms
open Lean
set_option pp.all true
set_option pp.universes true
set_option pp.proofs true
set_option pp.maxSteps 2000000
set_option pp.deepTerms true
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let modName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if modName == `Definitions || modName == `Checkers || modName == `Encoding || modName == `Enumeration || modName == `Rotations || modName == `IndexedCertificates || modName == `MaskSemantics || modName == `LabelBlocks || modName == `Data27 || modName == `Controls || modName == `Masks27 || modName == `Tree27_000 || modName == `Valid28_000 || modName == `Valid28_001 || modName == `Valid28_002 || modName == `Valid28_003 || modName == `Valid28_004 || modName == `Valid28_005 || modName == `Valid28_006 || modName == `Valid28_007 || modName == `Valid28_008 || modName == `Valid28_009 || modName == `Valid28_010 || modName == `Valid28_011 || modName == `Valid28_012 || modName == `Valid28_013 || modName == `Valid28_014 || modName == `Valid28_015 || modName == `Valid28_016 || modName == `Valid28_017 || modName == `Valid28_018 || modName == `Valid28_019 || modName == `Valid28_020 || modName == `Valid28_021 || modName == `Valid28_022 || modName == `Valid28_023 || modName == `Valid28_024 || modName == `Masks28 || modName == `Tree28_000 || modName == `Tree28_001 || modName == `Tree28_002 || modName == `Tree28_003 || modName == `Tree28_004 || modName == `Tree28_005 || modName == `Tree28_006 || modName == `Tree28_007 || modName == `Tree28_008 || modName == `Tree28_009 || modName == `Tree28_010 || modName == `Tree28_011 || modName == `Tree28_012 || modName == `Tree28_013 || modName == `Tree28_014 || modName == `Tree28_015 || modName == `Tree28_016 || modName == `Tree28_017 || modName == `Tree28_018 || modName == `Tree28_019 || modName == `Tree28_020 || modName == `Tree28_021 || modName == `Tree28_022 || modName == `Tree28_023 || modName == `Tree28_024 || modName == `Tree28_025 || modName == `Tree28_026 || modName == `Tree28_027 || modName == `Tree28_028 || modName == `Tree28_029 || modName == `Tree28_030 || modName == `Tree28_031 || modName == `Tree28_032 || modName == `Tree28_033 || modName == `Tree28_034 || modName == `Tree28_035 || modName == `Tree28_036 || modName == `Tree28_037 || modName == `Tree28_038 || modName == `Tree28_039 || modName == `Tree28_040 || modName == `Tree28_041 || modName == `Tree28_042 || modName == `Tree28_043 || modName == `Tree28_044 || modName == `Tree28_045 || modName == `Tree28_046 || modName == `Tree28_047 || modName == `Tree28_048 || modName == `Tree28_049 || modName == `Tree28_050 || modName == `Tree28_051 || modName == `Tree28_052 || modName == `Tree28_053 || modName == `Tree28_054 || modName == `Tree28_055 || modName == `Tree28_056 || modName == `Tree28_057 || modName == `Tree28_058 || modName == `Tree28_059 || modName == `Tree28_060 || modName == `Tree28_061 || modName == `Tree28_062 || modName == `Tree28_063 || modName == `Tree28_064 || modName == `Tree28_065 || modName == `Tree28_066 || modName == `Tree28_067 || modName == `Tree28_068 || modName == `Tree28_069 || modName == `Tree28_070 || modName == `Tree28_071 || modName == `Tree28_072 || modName == `Tree28_073 || modName == `Tree28_074 || modName == `Tree28_075 || modName == `Tree28_076 || modName == `Tree28_077 || modName == `Tree28_078 || modName == `Tree28_079 || modName == `Tree28_080 || modName == `Tree28_081 || modName == `Tree28_082 || modName == `Tree28_083 || modName == `Tree28_084 || modName == `Tree28_085 || modName == `Tree28_086 || modName == `Tree28_087 || modName == `Tree28_088 || modName == `Tree28_089 || modName == `Tree28_090 || modName == `Tree28_091 || modName == `Tree28_092 || modName == `Tree28_093 || modName == `Tree28_094 || modName == `Tree28_095 || modName == `Tree28_096 || modName == `Tree28_097 || modName == `Tree28_098 || modName == `Tree28_099 || modName == `Tree28_100 || modName == `Tree28_101 || modName == `Tree28_102 || modName == `Tree28_103 || modName == `Tree28_104 || modName == `Tree28_105 || modName == `Tree28_106 || modName == `Tree28_107 || modName == `Tree28_108 || modName == `Tree28_109 || modName == `Tree28_110 || modName == `Tree28_111 || modName == `Tree28_112 || modName == `Tree28_113 || modName == `Tree28_114 || modName == `Tree28_115 || modName == `Label27_000 || modName == `Label27_001 || modName == `Label27_002 || modName == `Label27_003 || modName == `Label27_004 || modName == `Label27_005 || modName == `Label27_006 || modName == `Label27_007 || modName == `Label27_008 || modName == `Label27_009 || modName == `Label27_010 || modName == `Label27_011 || modName == `Label27_012 || modName == `Label27_013 || modName == `Label27_014 || modName == `Label27_015 || modName == `Label27_016 || modName == `Label27_017 || modName == `Label27_018 || modName == `Label27_019 || modName == `Label27_020 || modName == `Label27_021 || modName == `Label27_022 || modName == `Label27_023 || modName == `Label27_024 || modName == `Label27_025 || modName == `Label27_026 || modName == `Label27_027 || modName == `Label27_028 || modName == `Label27_029 || modName == `Label27_030 || modName == `Label27_031 || modName == `Label27_032 || modName == `Label27_033 || modName == `Label27_034 || modName == `Label27_035 || modName == `Label27_036 || modName == `Label27_037 || modName == `Label27_038 || modName == `Label27_039 || modName == `Label27_040 || modName == `Label27_041 || modName == `Label27_042 || modName == `Label27_043 || modName == `Label27_044 || modName == `Label27_045 || modName == `Label27_046 || modName == `Label27_047 || modName == `Label27_048 || modName == `Label27_049 || modName == `Label27_050 || modName == `Label27_051 || modName == `LowerIndexed then
      count := count + 1
      let axs ← collectAxioms n
      let impl := Lean.Compiler.getImplementedBy? env n
      let ext := isExtern env n
      logInfo m!"DECL {n}\nMODULE {modName}\nUNSAFE {ci.isUnsafe}\nPARTIAL {ci.isPartial}\nIMPLEMENTED_BY {impl}\nEXTERN {ext}\nTYPE {ci.type}\nBODY {ci.value? (allowOpaque := true)}\nAXIOMS {axs}"
      if ci.isUnsafe || ci.isPartial || impl.isSome || ext || n.toString.endsWith "_unsafe_rec" then
        throwError "Forbidden declaration property: {n}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {n}"
  logInfo m!"TOTAL_LOCAL_DECLARATIONS {count}"
