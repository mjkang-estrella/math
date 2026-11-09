import YusterPolynomial
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace YusterCounterexample

def alphaLower : ℚ := 61/1000

def alphaUpper : ℚ := 613/10000

def samplePoints : List ℚ := [1/100,1/10,1/2,3/5,4/5]

def rhoCheck : Bool := samplePoints.all (fun x => decide (rhoEval 48 x<0))

def signCheck : Bool :=
  decide (alphaLower*rhoEval 48 (1/100)-sigmaEval 48 (1/100)<0) &&
  decide (0<alphaUpper*rhoEval 48 (1/10)-sigmaEval 48 (1/10)) &&
  decide (alphaLower*rhoEval 48 (1/2)-sigmaEval 48 (1/2)<0) &&
  decide (0<alphaUpper*rhoEval 48 (3/5)-sigmaEval 48 (3/5)) &&
  decide (alphaLower*rhoEval 48 (4/5)-sigmaEval 48 (4/5)<0)

theorem alphaLower_check : alphaLower*(1+alphaLower)^47<1 := by decide +kernel

theorem alphaUpper_check : 1<alphaUpper*(1+alphaUpper)^47 := by decide +kernel

theorem rhoCheck_ok : rhoCheck=true := by decide +kernel

theorem signCheck_ok : signCheck=true := by decide +kernel

end YusterCounterexample
