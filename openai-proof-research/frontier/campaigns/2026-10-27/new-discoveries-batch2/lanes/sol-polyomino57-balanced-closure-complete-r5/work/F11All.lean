import F11B000
import F11B001
import F11B002
import F11B003
import F11B004
import F11B005
import F11B006
import F11B007
import F11B008
import F11B009
import F11B010
import F11B011
import F11B012
import F11B013
import F11B014
import F11B015
import F11B016
import F11B017
import F11B018
import F11B019
import F11B020
import F11B021
import F11B022
import F11B023
import F11B024
import F11B025
import F11B026
import F11B027
import F11B028
import F11B029
import F11B030
import F11B031
import F11B032
import F11B033
import F11B034
import F11B035
import F11B036
import F11B037
import F11B038
import F11B039
import F11B040
import F11B041
import F11B042
import F11B043
import F11B044
import F11B045
import F11B046
import F11B047
import F11B048
import F11B049
import F11B050
import F11B051
import F11B052
import F11B053
import F11B054
import F11B055
import F11B056
import F11B057
import F11B058
import F11B059
import F11B060
import F11B061
import F11B062
import F11B063
import F11B064
import F11B065
import F11B066
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

def family11 : RowFamilyTree := (.branch (.branch (.branch (.branch (.branch (.branch F11B000 F11B001) (.branch F11B002 F11B003)) (.branch (.branch F11B004 F11B005) (.branch F11B006 F11B007))) (.branch (.branch (.branch F11B008 F11B009) (.branch F11B010 F11B011)) (.branch (.branch F11B012 F11B013) (.branch F11B014 F11B015)))) (.branch (.branch (.branch (.branch F11B016 F11B017) (.branch F11B018 F11B019)) (.branch (.branch F11B020 F11B021) (.branch F11B022 F11B023))) (.branch (.branch (.branch F11B024 F11B025) (.branch F11B026 F11B027)) (.branch (.branch F11B028 F11B029) (.branch F11B030 (.branch F11B031 F11B032)))))) (.branch (.branch (.branch (.branch (.branch F11B033 F11B034) (.branch F11B035 F11B036)) (.branch (.branch F11B037 F11B038) (.branch F11B039 F11B040))) (.branch (.branch (.branch F11B041 F11B042) (.branch F11B043 F11B044)) (.branch (.branch F11B045 F11B046) (.branch F11B047 (.branch F11B048 F11B049))))) (.branch (.branch (.branch (.branch F11B050 F11B051) (.branch F11B052 F11B053)) (.branch (.branch F11B054 F11B055) (.branch F11B056 F11B057))) (.branch (.branch (.branch F11B058 F11B059) (.branch F11B060 F11B061)) (.branch (.branch F11B062 F11B063) (.branch F11B064 (.branch F11B065 F11B066)))))))
theorem F11B000_lift (row : List GridPoint) (h : FamilyMember row F11B000) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001_lift (row : List GridPoint) (h : FamilyMember row F11B001) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002_lift (row : List GridPoint) (h : FamilyMember row F11B002) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003_lift (row : List GridPoint) (h : FamilyMember row F11B003) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004_lift (row : List GridPoint) (h : FamilyMember row F11B004) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005_lift (row : List GridPoint) (h : FamilyMember row F11B005) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006_lift (row : List GridPoint) (h : FamilyMember row F11B006) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007_lift (row : List GridPoint) (h : FamilyMember row F11B007) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008_lift (row : List GridPoint) (h : FamilyMember row F11B008) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009_lift (row : List GridPoint) (h : FamilyMember row F11B009) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010_lift (row : List GridPoint) (h : FamilyMember row F11B010) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011_lift (row : List GridPoint) (h : FamilyMember row F11B011) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012_lift (row : List GridPoint) (h : FamilyMember row F11B012) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013_lift (row : List GridPoint) (h : FamilyMember row F11B013) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014_lift (row : List GridPoint) (h : FamilyMember row F11B014) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015_lift (row : List GridPoint) (h : FamilyMember row F11B015) : FamilyMember row family11 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016_lift (row : List GridPoint) (h : FamilyMember row F11B016) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017_lift (row : List GridPoint) (h : FamilyMember row F11B017) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018_lift (row : List GridPoint) (h : FamilyMember row F11B018) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B019_lift (row : List GridPoint) (h : FamilyMember row F11B019) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020_lift (row : List GridPoint) (h : FamilyMember row F11B020) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021_lift (row : List GridPoint) (h : FamilyMember row F11B021) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022_lift (row : List GridPoint) (h : FamilyMember row F11B022) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023_lift (row : List GridPoint) (h : FamilyMember row F11B023) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024_lift (row : List GridPoint) (h : FamilyMember row F11B024) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025_lift (row : List GridPoint) (h : FamilyMember row F11B025) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026_lift (row : List GridPoint) (h : FamilyMember row F11B026) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B027_lift (row : List GridPoint) (h : FamilyMember row F11B027) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028_lift (row : List GridPoint) (h : FamilyMember row F11B028) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B029_lift (row : List GridPoint) (h : FamilyMember row F11B029) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030_lift (row : List GridPoint) (h : FamilyMember row F11B030) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031_lift (row : List GridPoint) (h : FamilyMember row F11B031) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))))
theorem F11B032_lift (row : List GridPoint) (h : FamilyMember row F11B032) : FamilyMember row family11 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))
theorem F11B033_lift (row : List GridPoint) (h : FamilyMember row F11B033) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B034_lift (row : List GridPoint) (h : FamilyMember row F11B034) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035_lift (row : List GridPoint) (h : FamilyMember row F11B035) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036_lift (row : List GridPoint) (h : FamilyMember row F11B036) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B037_lift (row : List GridPoint) (h : FamilyMember row F11B037) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B038_lift (row : List GridPoint) (h : FamilyMember row F11B038) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B039_lift (row : List GridPoint) (h : FamilyMember row F11B039) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040_lift (row : List GridPoint) (h : FamilyMember row F11B040) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041_lift (row : List GridPoint) (h : FamilyMember row F11B041) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042_lift (row : List GridPoint) (h : FamilyMember row F11B042) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B043_lift (row : List GridPoint) (h : FamilyMember row F11B043) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B044_lift (row : List GridPoint) (h : FamilyMember row F11B044) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B045_lift (row : List GridPoint) (h : FamilyMember row F11B045) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B046_lift (row : List GridPoint) (h : FamilyMember row F11B046) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B047_lift (row : List GridPoint) (h : FamilyMember row F11B047) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B048_lift (row : List GridPoint) (h : FamilyMember row F11B048) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))))
theorem F11B049_lift (row : List GridPoint) (h : FamilyMember row F11B049) : FamilyMember row family11 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))
theorem F11B050_lift (row : List GridPoint) (h : FamilyMember row F11B050) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051_lift (row : List GridPoint) (h : FamilyMember row F11B051) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B052_lift (row : List GridPoint) (h : FamilyMember row F11B052) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B053_lift (row : List GridPoint) (h : FamilyMember row F11B053) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B054_lift (row : List GridPoint) (h : FamilyMember row F11B054) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B055_lift (row : List GridPoint) (h : FamilyMember row F11B055) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B056_lift (row : List GridPoint) (h : FamilyMember row F11B056) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B057_lift (row : List GridPoint) (h : FamilyMember row F11B057) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B058_lift (row : List GridPoint) (h : FamilyMember row F11B058) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B059_lift (row : List GridPoint) (h : FamilyMember row F11B059) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060_lift (row : List GridPoint) (h : FamilyMember row F11B060) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B061_lift (row : List GridPoint) (h : FamilyMember row F11B061) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B062_lift (row : List GridPoint) (h : FamilyMember row F11B062) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B063_lift (row : List GridPoint) (h : FamilyMember row F11B063) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B064_lift (row : List GridPoint) (h : FamilyMember row F11B064) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B065_lift (row : List GridPoint) (h : FamilyMember row F11B065) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h)))))))
theorem F11B066_lift (row : List GridPoint) (h : FamilyMember row F11B066) : FamilyMember row family11 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))
end Polyomino57
