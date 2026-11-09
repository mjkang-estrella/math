import ColouredSeed
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed32Open5
def colouring : FactorColouring decomposition0 (by decide : 2 ≤ 5) where
  colour := ![true,true,true,true,false,false,false,true,true,true,true,false,false,false,true,true,false,false,false,false,true,false,true,false,true,false,true,false,false,false,true,true]
  proper0 := by decide
  proper1 := by decide
def orientedWalk : Base32Open5.graph.Walk 0 0 := (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 0 18) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 18 3) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 3 16) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 16 30) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 30 19) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 19 24) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 24 25) (SimpleGraph.Walk.cons (by decide : Base32Open5.graph.Adj 25 0) SimpleGraph.Walk.nil))))))))
def coloured : ColouredSeed Base32Open5.graph 5 5 false where
  seed := seed
  strong := by decide
  colouring := colouring
  walk := orientedWalk
  isCycle := by
    change @SimpleGraph.Walk.IsCycle _ Base32Open5.graph 0 orientedWalk
    rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  length_eq := by decide
  indexed := by decide
  starts_true := by decide
  oriented := by
    dsimp [orientedWalk, OmegaWalk]
    decide
end XorMagic.Seed32Open5
