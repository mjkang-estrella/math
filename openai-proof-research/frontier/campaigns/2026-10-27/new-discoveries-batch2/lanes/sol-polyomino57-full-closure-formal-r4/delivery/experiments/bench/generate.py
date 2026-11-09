import os,resource,signal,json,hashlib
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent
pt=lambda p:'(%d,%d)'%tuple(p)
cells=lambda P:'['+','.join(map(pt,P))+']'
def norm(P):
 x=min(a for a,b in P);y=min(b for a,b in P)
 return tuple(sorted((a-x,b-y) for a,b in P)),(-x,-y)
def nbr(P):return {(x+dx,y+dy) for x,y in P for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]}-set(P)
layers=[[((0,0),)]]
for k in range(7):layers.append(sorted({norm(set(P)|{b})[0] for P in layers[-1] for b in nbr(P)}))
mods=[]
for size in [8]:
 name='Layer%d'%size;mods.append(name)
 (L/'formal'/(name+'.lean')).write_text('import LocalAssembly\nset_option autoImplicit false\nnamespace Polyomino57\ndef layer%d : Array (List GridPoint) := #['%size+','.join(map(cells,layers[size-1]))+']\nend Polyomino57\n')
for size in [7]:
 source=layers[size-1];target=layers[size];lookup={P:i for i,P in enumerate(target)};chunknames=[]
 for start in range(0,len(source),8):
  name='Closure%dC%03d'%(size,start//8);mods.append(name);chunknames.append(name)
  s=['import Layer%d'%(size+1),'set_option autoImplicit false','set_option maxRecDepth 65536','set_option maxHeartbeats 10000000','namespace Polyomino57'];names=[]
  for j,P in enumerate(source[start:start+8],start):
   nm='row%d_%d'%(size,j);names.append(nm)
   edges=[]
   for b in sorted(nbr(P)):
    Q,t=norm(set(P)|{b});edges.append('('+pt(b)+',('+str(lookup[Q])+','+pt(t)+'))')
   s += ['def '+nm+' : List GridPoint := '+cells(P),'def '+nm+'choice (b : GridPoint) : ℕ × GridPoint := ((['+','.join(edges)+'] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))','theorem '+nm+'_checked : successorFastRowCheck layer%d '%(size+1)+nm+' '+nm+'choice = true := by decide']
  s += ['def '+name+'rows : List (List GridPoint) := ['+','.join(names)+']', 'theorem '+name+'_closed : ∀ row ∈ '+name+'rows, ∃ choice, successorFastRowCheck layer%d row choice = true := by'%(size+1),'  intro row hr','  simp only ['+name+'rows,List.mem_cons,List.not_mem_nil,or_false] at hr','  rcases hr with '+ ' | '.join('h%d'%i for i in range(len(names)))]
  for i,nm in enumerate(names):s+=['  · subst row','    exact ⟨'+nm+'choice,'+nm+'_checked⟩']
  s+=['end Polyomino57'];(L/'formal'/(name+'.lean')).write_text('\n'.join(s)+'\n')
 name='Closure%d'%size;mods.append(name)
 s=['import '+n for n in chunknames]+['set_option autoImplicit false','namespace Polyomino57','def closedLayer%d : Array (List GridPoint) := ('%size+' ++ ('.join(n+'rows' for n in chunknames)+')'*(len(chunknames)-1)+').toArray','theorem closure%d_local : LocallyClosed closedLayer%d layer%d := by'%(size,size,size+1),'  intro row hr','  simp only [closedLayer%d,List.toList_toArray,List.mem_append] at hr'%size,'  rcases hr with '+' | '.join('h%d'%i for i in range(len(chunknames)))]
 for i,n in enumerate(chunknames):s+=['  · exact '+n+'_closed row h%d'%i]
 s+=['theorem closure%d : ∃ choices, arrayClosureCheck closedLayer%d layer%d choices = true :='%(size,size,size+1),'  locallyClosed_array closure%d_local'%size,'end Polyomino57']
 (L/'formal'/(name+'.lean')).write_text('\n'.join(s)+'\n')
(L/'generated-modules.json').write_text(json.dumps(mods,indent=2))
