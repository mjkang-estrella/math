import Seed16Closed4
import Seed16Open5
import Seed32Closed4
import Seed32Open5
namespace XorMagic
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The stronger cycle interface needed for simple-cycle persistence. -/
structure StrongFactorCycleData (G : SimpleGraph V) (d : ℕ) extends FactorCycleData G d where
  three_le : 3 ≤ length

def Seed16Closed4.strongCycle : StrongFactorCycleData Base16Closed4.graph 4 where
  toFactorCycleData := Seed16Closed4.factorCycle
  three_le := by decide

def Seed16Open5.strongCycle : StrongFactorCycleData Base16Open5.graph 5 where
  toFactorCycleData := Seed16Open5.factorCycle
  three_le := by decide

def Seed32Closed4.strongCycle : StrongFactorCycleData Base32Closed4.graph 4 where
  toFactorCycleData := Seed32Closed4.factorCycle
  three_le := by decide

def Seed32Open5.strongCycle : StrongFactorCycleData Base32Open5.graph 5 where
  toFactorCycleData := Seed32Open5.factorCycle
  three_le := by decide
end XorMagic
