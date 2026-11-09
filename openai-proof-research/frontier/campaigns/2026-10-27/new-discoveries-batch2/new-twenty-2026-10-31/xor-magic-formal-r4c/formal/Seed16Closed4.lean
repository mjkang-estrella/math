import Base16Closed4
import SeedStructure
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed16Closed4
def mates0 : Fin 4 → Fin 16 → Fin 16 := ![![9,2,1,14,5,4,10,12,13,0,6,15,7,8,3,11],![13,14,11,4,3,12,15,8,7,10,9,2,5,0,1,6],![15,10,7,12,8,14,11,2,4,13,1,6,3,9,5,0],![11,7,15,5,10,3,8,1,6,14,4,0,13,12,9,2]]
def decomposition0 : MatchingDecomposition (Base16Closed4.graph) 4 where
  mate := mates0
  involutive := by decide
  no_fixed := by decide
  distinct := by decide
  cover := by decide
def mates1 : Fin 11 → Fin 16 → Fin 16 := ![![14,4,8,11,1,9,12,13,2,5,15,3,6,7,0,10],![8,15,5,9,6,2,4,14,0,3,12,13,10,11,7,1],![2,13,0,10,12,8,9,15,5,6,3,14,4,1,11,7],![4,8,10,15,0,11,7,6,1,12,2,5,9,14,13,3],![3,5,4,0,2,1,13,11,10,15,8,7,14,6,12,9],![12,9,14,6,11,7,3,5,15,1,13,4,0,10,2,8],![5,6,9,7,13,0,1,3,14,2,11,10,15,4,8,12],![6,11,3,2,15,13,0,9,12,7,14,1,8,5,10,4],![7,12,6,8,14,10,2,0,3,11,5,9,1,15,4,13],![1,0,12,13,9,6,5,10,11,4,7,8,2,3,15,14],![10,3,13,1,7,15,14,4,9,8,0,12,11,2,6,5]]
def decomposition1 : MatchingDecomposition (Base16Closed4.graphᶜ) 11 where
  mate := mates1
  involutive := by decide
  no_fixed := by decide
  distinct := by decide
  cover := by decide
def cycle : Fin 16 → Fin 16 := ![0,9,10,6,15,11,2,1,14,3,4,5,12,7,8,13]
def factorCycle : FactorCycleData Base16Closed4.graph 4 where
  factors := decomposition0
  complementFactors := decomposition1
  two_le := by decide
  length := 16
  positive := by decide
  not_three := by decide
  cycle := cycle
  injective := by decide
  edges := by decide
def seed : LiftSeed Base16Closed4.graph 4 4 true where
  regular := Base16Closed4.regular
  magic := Base16Closed4.magic
  factorCycle := factorCycle
end XorMagic.Seed16Closed4
