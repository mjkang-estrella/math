from pathlib import Path
import re
mods=['ChordCore','ChordRepresentative','ChordSanity','ChordSmall','ChordBridgeChecks','ChordControls']
words=['11234234','12134234','12314234','12341234']
for k in range(4):
 p=Path(f'ChordFour{k}.lean');s=p.read_text();a=s.index(f'theorem exception{k}_chunk0');b=s.index(f'theorem exception{k}_raw')
 Path(f'ChordFourBase{k}.lean').write_text(s[:a]+'end Chord\n');mods.append(f'ChordFourBase{k}')
 chunks=re.split(r'(?=theorem exception\d_chunk\d+ :)',s[a:b]);chunks=[c for c in chunks if c.strip()]
 for g in range(4):
  name=f'ChordFourChunk{k}_{g}'
  Path(name+'.lean').write_text(f'import ChordFourBase{k}\nnamespace Chord\nset_option maxRecDepth 10000\nset_option maxHeartbeats 6000000\n'+''.join(chunks[4*g:4*g+4])+'end Chord\n');mods.append(name)
 tail=s[b:]
 # Small independent 3-half-edge boundary evaluator for explicit witnesses.
 w=words[k];t=[next(j for j in range(8) if j!=i and w[j]==w[i]) for i in range(8)]
 def boundary(m):
  f=[]
  for h in range(24):
   i,q=divmod(h,3);j=(i-1)%8 if q==0 else (i+1)%8 if q==1 else t[i]
   q=1 if q==0 else 0 if q==1 else 2
   f.append(3*j+((2,0,1) if m>>j&1 else (1,2,0))[q])
  seen=set();b=0
  for h in range(24):
   if h not in seen:
    b+=1
    while h not in seen:seen.add(h);h=f[h]
  return b
 for g in [1,2]:
  m=next(m for m in range(256) if 2*g+boundary(m)==6)
  name='one' if g==1 else 'two'
  tail=re.sub(rf'theorem exception{k}_{name} :.*?(?=theorem )',f'theorem exception{k}_{name} : ∃ c : Sides 4, HasGenus exception{k} c {g} := ⟨maskSides 4 {m}, by decide⟩\n',tail,flags=re.S)
 Path(f'ChordFour{k}.lean').write_text(''.join(f'import ChordFourChunk{k}_{g}\n' for g in range(4))+'namespace Chord\n'+tail)
 mods.append(f'ChordFour{k}')
mods+=['ChordFourWitnesses','ChordRemaining','ChordFinal']
Path('modules.txt').write_text('\n'.join(mods)+'\n')
