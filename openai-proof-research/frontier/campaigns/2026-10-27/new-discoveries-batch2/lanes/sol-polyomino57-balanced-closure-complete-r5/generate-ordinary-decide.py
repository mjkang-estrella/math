from pathlib import Path
import json,resource,signal,sys
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,65));signal.alarm(90)
L=Path(__file__).resolve().parent;W=L/'work'
cells=lambda P:'['+','.join('(%d,%d)'%tuple(p) for p in P)+']'
pt=lambda p:'(%d,%d)'%tuple(p)
header='set_option autoImplicit false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 10000000\nnamespace Polyomino57\n'
def balance(xs):
 if len(xs)==1:return xs[0]
 m=len(xs)//2;return '(.branch '+balance(xs[:m])+' '+balance(xs[m:])+')'
def path(n,i):
 if n==1:return []
 m=n//2
 return [False]+path(m,i) if i<m else [True]+path(n-m,i-m)
def lift(path,h='h'):
 for b in reversed(path):h='Or.in'+('r' if b else 'l')+' ('+h+')'
 return h
if sys.argv[1]=='trees':
 mods=[]
 for size in [7,8,9,10,11]:
  rows=[json.loads(s) for s in (L/'data'/f'layer{size}.jsonl').read_text().splitlines()];blocks=[]
  for start in range(0,len(rows),2048):
   nm=f'F{size}B{start//2048:03d}';blocks.append(nm);leaves=[];s=['import FamilyTree\n'+header]
   for k in range(start,min(start+2048,len(rows)),32):
    leaf=nm+'L%d'%((k-start)//32);leaves.append(leaf)
    s+=['def '+leaf+' : RowFamilyTree := .leaf #['+','.join(cells(P) for P in rows[k:min(k+32,start+2048)])+']']
   s+=['def '+nm+' : RowFamilyTree := '+balance(leaves)]
   for j,leaf in enumerate(leaves):s += [f'theorem {leaf}_lift (row : List GridPoint) (h : FamilyMember row {leaf}) : FamilyMember row {nm} := by\n  exact '+lift(path(len(leaves),j))]
   (W/(nm+'.lean')).write_text('\n'.join(s)+'\nend Polyomino57\n');mods.append(nm)
  nm=f'F{size}All';s=['\n'.join('import '+m for m in blocks)+'\n'+header,f'def family{size} : RowFamilyTree := '+balance(blocks)]
  for j,b in enumerate(blocks):s +=[f'theorem {b}_lift (row : List GridPoint) (h : FamilyMember row {b}) : FamilyMember row family{size} := by\n  exact '+lift(path(len(blocks),j))]
  (W/(nm+'.lean')).write_text('\n'.join(s)+'\nend Polyomino57\n');mods.append(nm)
 (L/'tree-modules.json').write_text(json.dumps(mods,indent=2))
elif sys.argv[1]=='batch':
 size,start,count=map(int,sys.argv[2:]);rows=[json.loads(s) for s in (L/'data'/f'layer{size}.jsonl').read_text().splitlines()];targets=[json.loads(s) for s in (L/'data'/f'layer{size+1}.jsonl').read_text().splitlines()]
 records={i:json.loads(s) for i,s in enumerate((L/'closure-path-data'/f'closure{size}.jsonl').open()) if start<=i<start+count};name=f'C{size}R{start:05d}';s=[f'import F{size+1}All\nimport F{size}B{start//2048:03d}\n'+header]
 for i in range(start,min(start+count,len(rows))):
  r=f'c{size}r{i}';P=rows[i];es=records[i]['edges']
  s += [f'theorem {r}_closed : FamilyRowClosed (fun S => FamilyMember S family{size+1}) '+cells(P)+' := by',f'  let {r}targets : Array (List GridPoint) := #['+','.join(cells(targets[e[1]]) for e in es)+']',f'  let {r}choice (b : GridPoint) : ℕ × GridPoint := ((['+','.join('('+pt(e[0])+',('+str(j)+','+pt(e[2])+'))' for j,e in enumerate(es))+'] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))',f'  have checked : successorFastRowCheck {r}targets '+cells(P)+f' {r}choice = true := by decide',f'  refine ⟨{r}targets, {r}choice, ?_, checked⟩\n  intro S h\n  simp only [{r}targets, List.mem_cons, List.not_mem_nil, or_false] at h\n  rcases h with '+' | '.join('h' for _ in es)]
  for e in es:
   idx=e[1];b=f'F{size+1}B{idx//2048:03d}';leaf=b+f'L{(idx%2048)//32}'
   pathlit='['+','.join('true' if v else 'false' for v in e[3])+']'
   s += [f'  · subst S\n    exact familyLookup_sound family{size+1} {pathlit} {e[4]} _ (by rfl)']
 leaf=f'F{size}B{start//2048:03d}L{(start%2048)//32}'
 if start%32==0 and count==32:
  s += [f'theorem {name}_closed (row : List GridPoint) (h : FamilyMember row {leaf}) : FamilyRowClosed (fun S => FamilyMember S family{size+1}) row := by\n  simp only [{leaf}, FamilyMember, List.mem_cons, List.not_mem_nil, or_false] at h\n  rcases h with '+' | '.join('h' for _ in rows[start:start+32])]
  for i in range(start,min(start+32,len(rows))):s += [f'  · subst row; exact c{size}r{i}_closed']
 source='\n'.join(s)
 marker='theorem '+name+'_closed'
 if marker in source:
  import re
  before,after=source.split(marker,1)
  preamble,allrows=before.split('namespace Polyomino57',1)
  proofs=re.split(r'(?=theorem c[0-9]+r[0-9]+_closed)',allrows.strip())
  proofs=[x.strip() for x in proofs if x.strip()]
  groups=[]
  for off in range(0,len(proofs),8):
   inds=list(range(start+off,min(start+off+8,len(rows),start+count)))
   g=name+f'G{off//8}'
   gh=f'theorem {g} (row : List GridPoint) (h : row ∈ ['+','.join(cells(rows[i]) for i in inds)+f']) : FamilyRowClosed (fun S => FamilyMember S family{size+1}) row := by\n'
   local='\n'.join(proofs[off:off+8]).replace('theorem ', 'have ')
   gh+='\n'.join('  '+line for line in local.splitlines())+'\n'
   gh+='  simp only [List.mem_cons, List.not_mem_nil, or_false] at h\n  rcases h with '+' | '.join('h' for i in inds)+'\n'
   gh+='\n'.join(f'  · subst row; exact c{size}r{i}_closed' for i in inds)
   groups.append(gh)
  head,body=(marker+after).split(' := by\n',1)
  body=body[:body.index('  · subst row')]
  body+='\n'.join(f'  · subst row; exact {name}G{off//8} _ (List.mem_of_getElem? (i := {off%8}) (by rfl))' for off in range(len(proofs)))
  source=preamble+'namespace Polyomino57\n'+'\n'.join(groups)+'\n'+head+' := by\n'+body
 (W/(name+'.lean')).write_text(source+'\nend Polyomino57\n');print(name)
