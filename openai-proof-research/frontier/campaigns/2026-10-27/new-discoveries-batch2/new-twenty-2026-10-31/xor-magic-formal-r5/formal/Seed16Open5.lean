import Base16Open5
import SeedStructure
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed16Open5
def mates0 : Fin 5 → Fin 16 → Fin 16 := ![![12,15,13,10,11,7,14,5,9,8,3,4,0,2,6,1],![14,11,10,5,12,3,9,15,13,6,2,1,4,8,0,7],![6,13,11,14,15,10,0,8,7,12,5,2,9,1,3,4],![9,7,5,6,14,2,3,1,12,0,15,13,8,11,4,10],![13,14,9,7,6,12,4,3,15,2,11,10,5,0,1,8]]
def decomposition0 : MatchingDecomposition (Base16Open5.graph) 5 where
  mate := mates0
  involutive := by decide
  no_fixed := by decide
  distinct := by decide
  cover := by decide
def mates1 : Fin 10 → Fin 16 → Fin 16 := ![![8,6,12,15,10,14,1,11,0,13,4,7,2,9,5,3],![3,10,7,0,5,4,15,2,11,14,1,8,13,12,9,6],![5,3,6,1,13,0,2,10,14,15,7,12,11,4,8,9],![11,2,1,12,9,15,8,14,6,4,13,0,3,10,7,5],![7,4,14,11,1,8,12,0,5,10,9,3,6,15,2,13],![1,0,4,9,2,6,5,13,10,3,8,14,15,7,11,12],![2,5,0,13,8,1,10,12,4,11,6,9,7,3,15,14],![4,12,15,8,0,11,13,9,3,7,14,5,1,6,10,2],![15,8,3,2,7,9,11,4,1,5,12,6,10,14,13,0],![10,9,8,4,3,13,7,6,2,1,0,15,14,5,12,11]]
def decomposition1 : MatchingDecomposition (Base16Open5.graphᶜ) 10 where
  mate := mates1
  involutive := by decide
  no_fixed := by decide
  distinct := by decide
  cover := by decide
def cycle : Fin 16 → Fin 16 := ![0,12,4,11,1,15,7,5,3,10,2,13,8,9,6,14]
def factorCycle : FactorCycleData Base16Open5.graph 5 where
  factors := decomposition0
  complementFactors := decomposition1
  two_le := by decide
  length := 16
  positive := by decide
  not_three := by decide
  cycle := cycle
  injective := by decide
  edges := by decide
def seed : LiftSeed Base16Open5.graph 4 5 false where
  regular := Base16Open5.regular
  magic := Base16Open5.magic
  factorCycle := factorCycle
end XorMagic.Seed16Open5
