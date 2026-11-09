import ColouredSeed
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed32Closed4
def colouring : FactorColouring decomposition0 (by decide : 2 ≤ 4) where
  colour := ![true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,true,true,false,true,false,true,true,true,true,true,false,false,false,false,true,false]
  proper0 := by decide
  proper1 := by decide
def orientedWalk : Base32Closed4.graph.Walk 0 0 := (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 0 12) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 12 24) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 24 6) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 6 15) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 15 14) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 14 17) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 17 1) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 1 9) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 9 31) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 31 19) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 19 10) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 10 22) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 22 26) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 26 30) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 30 27) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 27 3) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 3 11) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 11 21) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 21 29) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 29 25) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 25 7) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 7 23) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 23 20) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 20 13) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 13 8) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 8 4) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 4 28) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 28 16) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 16 18) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 18 5) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 5 2) (SimpleGraph.Walk.cons (by decide : Base32Closed4.graph.Adj 2 0) SimpleGraph.Walk.nil))))))))))))))))))))))))))))))))
def coloured : ColouredSeed Base32Closed4.graph 5 4 true where
  seed := seed
  strong := by decide
  colouring := colouring
  walk := orientedWalk
  isCycle := by
    change @SimpleGraph.Walk.IsCycle _ Base32Closed4.graph 0 orientedWalk
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  length_eq := by decide
  indexed := by decide
  starts_true := by decide
  oriented := by
    dsimp [orientedWalk, OmegaWalk]
    decide
end XorMagic.Seed32Closed4
