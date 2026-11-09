from pathlib import Path
for k in range(4):
 p=Path(f'ChordFour{k}.lean');s=p.read_text();a=s.index('  all_goals first');b=s.index(f'theorem exception{k}_values')
 masks=[sum(((j>>(3-i))&1)<<i for i in range(4)) for j in range(16)]
 s=s[:a]+''.join(f'  · exact exception{k}_chunk{mask} b4 b5 b6 b7\n' for mask in masks)+s[b:]
 p.write_text(s)
 (Path('fresh-extraction')/p).write_text(s)
