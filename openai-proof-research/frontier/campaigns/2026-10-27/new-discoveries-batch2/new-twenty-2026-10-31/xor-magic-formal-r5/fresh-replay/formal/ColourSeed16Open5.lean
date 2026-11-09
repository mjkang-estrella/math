import ColouredSeed
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed16Open5
def colouring : FactorColouring decomposition0 (by decide : 2 ≤ 5) where
  colour := ![true,true,true,true,true,false,true,true,true,false,false,false,false,false,false,false]
  proper0 := by decide
  proper1 := by decide
def orientedWalk : Base16Open5.graph.Walk 0 0 := (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 0 12) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 12 4) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 4 11) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 11 1) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 1 15) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 15 7) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 7 5) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 5 3) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 3 10) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 10 2) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 2 13) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 13 8) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 8 9) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 9 6) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 6 14) (SimpleGraph.Walk.cons (by decide : Base16Open5.graph.Adj 14 0) SimpleGraph.Walk.nil))))))))))))))))
def coloured : ColouredSeed Base16Open5.graph 4 5 false where
  seed := seed
  strong := by decide
  colouring := colouring
  walk := orientedWalk
  isCycle := by
    change @SimpleGraph.Walk.IsCycle _ Base16Open5.graph 0 orientedWalk
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  length_eq := by decide
  indexed := by decide
  starts_true := by decide
  oriented := by
    dsimp [orientedWalk, OmegaWalk]
    decide
end XorMagic.Seed16Open5
