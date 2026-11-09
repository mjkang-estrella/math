from pathlib import Path
files=sorted(Path('src').glob('S[0-9][0-9].lean'))+sorted(Path('src').glob('T[0-9][0-9].lean'))
s=''.join(f'import {p.stem}\n' for p in files)+'namespace Smyth1512\n'
for label,b,a,lst in [('S',19,20,'SL'),('T',20,19,'TL')]:
 s+=f'theorem {lst}_length : {lst}.length = '+('1137' if label=='S' else '1134')+' := by\n'
 s+=f'  change (((comps 3 {b}) ×ˢ comps 2 {a}).filter _).length = _\n  rw [count_rows]\n'
 s+='  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, '
 s+=', '.join('count_'+p.stem for p in files if p.stem.startswith(label))+']\n  norm_num\n'
s+='end Smyth1512\n'
Path('src/Counts.lean').write_text(s)
