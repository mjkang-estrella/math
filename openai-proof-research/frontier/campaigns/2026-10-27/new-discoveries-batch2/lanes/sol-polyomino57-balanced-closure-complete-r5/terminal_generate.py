from pathlib import Path
import json,ast,sys,resource,signal,shutil
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;W=L/'work';R=L.parent/'sol-polyomino57-full-closure-formal-r4';start,count=map(int,sys.argv[1:]);name=f'TR{start:06d}'
rows={i:json.loads(s) for i,s in enumerate((L/'data/layer11.jsonl').open()) if start<=i<start+count}
records=[json.loads(s) for i,s in enumerate((R/'terminal-correspondence.jsonl').open()) if start<=i<start+count]
chunks={};imports=set();chunk_counts={}
for e in records:
 chunk=e['forest_chunk'];mod=chunk.split('c')[0];imports.add(mod)
 if chunk not in chunks:
  src=L.parent/'sol-polyomino57-efficient-certificate-r2/formal'/(mod+'.lean')
  if not (W/src.name).exists():shutil.copyfile(src,W/src.name)
  chunk_counts[mod]=sum(1 for line in src.read_text().splitlines() if line.startswith('def '+mod+'c') and ' : List ' in line)
  for line in src.read_text().splitlines():
   if line.startswith('def '+chunk+' : List '):chunks[chunk]=ast.literal_eval(line.split(' := ',1)[1])
pt=lambda p:'(%d,%d)'%tuple(p)
cells=lambda P:'['+','.join(map(pt,P))+']'
b=f'F11B{start//2048:03d}';leaf=b+f'L{start%2048//32}'
s=['\n'.join('import '+m for m in sorted(imports))+f'\nimport {b}\nset_option autoImplicit false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 10000000\nnamespace Polyomino57']
def path(n,i):
 if n==1:return []
 m=n//2
 return [False]+path(m,i) if i<m else [True]+path(n-m,i-m)
for e in records:
 i=e['generated_index'];chunk=e['forest_chunk'];idx=e['chunk_index'];raw,u=chunks[chunk][idx];t=e['generated_placement'];r=f'tr{i}';pair='('+cells(raw)+','+pt(u)+')';P=cells(rows[i])
 forest=chunk.split('c')[0];term=f'List.mem_of_getElem? (i := {idx}) (by rfl)'
 for bit in reversed(path(chunk_counts[forest],int(chunk.split('c')[1]))):term='Or.in'+('r' if bit else 'l')+' ('+term+')'
 s += [f'theorem {r}_placed : ∃ t, translate t ({P} : List GridPoint).toFinset ⊆ witness := by\n  refine ⟨{pt(t)}, ?_⟩\n  have hm : TreeMember {pair} {forest} := {term}\n  have hs := treeCheck_sound {forest} {forest}_checked {pair} hm\n  have hl : shiftedCells ({P} : List GridPoint) {pt(t)} = shiftedCells ({cells(raw)} : List GridPoint) {pt(u)} := by rfl\n  have he := congrArg List.toFinset hl\n  simp only [shiftedCells_semantics] at he\n  rw [he]\n  exact hs']
if count==32:
 s += [f'theorem {name}_placed (row : List GridPoint) (h : FamilyMember row {leaf}) : ∃ t, translate t row.toFinset ⊆ witness := by\n  simp only [{leaf}, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h\n  rcases h with '+' | '.join('h' for _ in records)]
 for e in records:s += [f'  · subst row; exact tr{e["generated_index"]}_placed']
source='\n'.join(s)
marker='theorem '+name+('_closed' if name.startswith('C') else '_placed')
if marker in source:
 before,after=source.split(marker,1)
 preamble,rows=before.split('namespace Polyomino57',1)
 head,body=(marker+after).split(' := by\n',1)
 rows=rows.strip().replace('\ntheorem ', '\nhave ')
 if rows.startswith('theorem '):rows='have '+rows[len('theorem '):]
 source=preamble+'namespace Polyomino57\n'+head+' := by\n'+'\n'.join('  '+line for line in rows.splitlines())+'\n'+body
(W/(name+'.lean')).write_text(source+'\nend Polyomino57\n');print(name)
