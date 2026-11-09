from pathlib import Path
import re,ast
for base in ['16Closed4','16Open5','32Closed4','32Open5']:
 s=Path('formal/Seed'+base+'.lean').read_text()
 mates=ast.literal_eval(re.search(r'def mates0.*? := (.*)',s)[1].replace('!',''))
 cyc=ast.literal_eval(re.search(r'def cycle.*? := (.*)',s)[1].replace('!',''))
 m=len(mates[0]); b=[None]*m
 for start in [cyc[0]]+list(range(m)):
  if b[start] is not None:continue
  b[start]=True;queue=[start]
  for v in queue:
   for ma in mates[:2]:
    w=ma[v]
    if b[w] is None:b[w]=not b[v];queue.append(w)
    assert b[w]!=b[v]
 assert all(mates[i%2][cyc[i]]==cyc[(i+1)%len(cyc)] for i in range(len(cyc)))
 walk='SimpleGraph.Walk.nil'
 for v,w in reversed(list(zip(cyc,cyc[1:]+cyc[:1]))):
  walk=f'(SimpleGraph.Walk.cons (by decide : Base{base}.graph.Adj {v} {w}) {walk})'
 text=f'''import ColouredSeed
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace XorMagic.Seed{base}
def colouring : FactorColouring decomposition0 (by decide : 2 ≤ {len(mates)}) where
  colour := ![{','.join(str(z).lower() for z in b)}]
  proper0 := by decide
  proper1 := by decide
def orientedWalk : Base{base}.graph.Walk {cyc[0]} {cyc[0]} := {walk}
def coloured : ColouredSeed Base{base}.graph {4 if m==16 else 5} {len(mates)} {str('Closed' in base).lower()} where
  seed := seed
  strong := by decide
  colouring := colouring
  walk := orientedWalk
  isCycle := by decide
  length_eq := by decide
  indexed := by decide
  starts_true := by decide
  oriented := by decide
end XorMagic.Seed{base}
'''
 Path('formal/ColourSeed'+base+'.lean').write_text(text)
