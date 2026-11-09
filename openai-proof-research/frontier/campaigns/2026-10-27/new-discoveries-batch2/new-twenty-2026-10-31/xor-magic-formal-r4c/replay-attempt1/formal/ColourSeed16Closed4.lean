import ColouredSeed
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed16Closed4
def colouring : FactorColouring decomposition0 (by decide : 2 ≤ 4) where
  colour := ![true,false,true,false,true,false,false,false,true,false,true,false,true,false,true,true]
  proper0 := by decide
  proper1 := by decide
def orientedWalk : Base16Closed4.graph.Walk 0 0 := (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 0 9) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 9 10) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 10 6) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 6 15) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 15 11) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 11 2) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 2 1) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 1 14) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 14 3) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 3 4) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 4 5) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 5 12) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 12 7) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 7 8) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 8 13) (SimpleGraph.Walk.cons (by decide : Base16Closed4.graph.Adj 13 0) SimpleGraph.Walk.nil))))))))))))))))
def coloured : ColouredSeed Base16Closed4.graph 4 4 true where
  seed := seed
  strong := by decide
  colouring := colouring
  walk := orientedWalk
  isCycle := by
    change @SimpleGraph.Walk.IsCycle _ Base16Closed4.graph 0 orientedWalk
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  length_eq := by decide
  indexed := by decide
  starts_true := by decide
  oriented := by
    dsimp [orientedWalk, OmegaWalk]
    decide
end XorMagic.Seed16Closed4
