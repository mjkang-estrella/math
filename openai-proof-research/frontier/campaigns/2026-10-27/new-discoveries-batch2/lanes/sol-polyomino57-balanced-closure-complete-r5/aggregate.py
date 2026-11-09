from pathlib import Path
import resource,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;W=L/'work';mods=[]
def elim(names):
 if len(names)==1:return names[0]+' row h'
 m=len(names)//2;return 'h.elim (fun h => '+elim(names[:m])+') (fun h => '+elim(names[m:])+')'
for size in [7,8,9,10]:
 n=sum(1 for _ in (L/'data'/f'layer{size}.jsonl').open());blocks=[]
 for start in range(0,n,2048):
  block=f'F{size}B{start//2048:03d}';nm=block+'Closed';blocks.append(nm)
  batches=[f'C{size}R{k:05d}' for k in range(start,min(start+2048,n),32)]
  s='\n'.join('import '+b for b in batches)+'\nset_option autoImplicit false\nnamespace Polyomino57\n'
  s+=f'theorem {nm} (row : List GridPoint) (h : FamilyMember row {block}) : FamilyRowClosed (fun S => FamilyMember S family{size+1}) row := by\n  exact '+elim([b+'_closed' for b in batches])+'\nend Polyomino57\n'
  (W/(nm+'.lean')).write_text(s);mods.append(nm)
 nm=f'Stage{size}Closed';s='\n'.join('import '+b for b in blocks)+f'\nimport F{size}All\nset_option autoImplicit false\nnamespace Polyomino57\n'
 s+=f'theorem stage{size}_closed (row : List GridPoint) (h : FamilyMember row family{size}) : FamilyRowClosed (fun S => FamilyMember S family{size+1}) row := by\n  exact '+elim(blocks)+'\nend Polyomino57\n'
 (W/(nm+'.lean')).write_text(s);mods.append(nm)
(L/'aggregation-modules.json').write_text(json.dumps(mods,indent=2))
