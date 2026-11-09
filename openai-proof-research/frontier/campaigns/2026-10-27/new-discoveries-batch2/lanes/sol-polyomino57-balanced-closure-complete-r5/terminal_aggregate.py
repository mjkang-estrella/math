from pathlib import Path
import resource,signal,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;W=L/'work';n=sum(1 for _ in (L/'data/layer11.jsonl').open());mods=[];blocks=[]
def elim(ns):
 if len(ns)==1:return ns[0]+' row h'
 m=len(ns)//2;return 'h.elim (fun h => '+elim(ns[:m])+') (fun h => '+elim(ns[m:])+')'
for start in range(0,n,2048):
 block=f'F11B{start//2048:03d}';name=block+'Placed';blocks.append(name)
 batches=[f'TR{k:06d}' for k in range(start,min(start+2048,n),32)]
 s='\n'.join('import '+b for b in batches)+'\nset_option autoImplicit false\nnamespace Polyomino57\n'
 s+=f'theorem {name} (row : List GridPoint) (h : FamilyMember row {block}) : ∃ t, translate t row.toFinset ⊆ witness := by\n  exact '+elim([b+'_placed' for b in batches])+'\nend Polyomino57\n'
 (W/(name+'.lean')).write_text(s);mods.append(name)
s='\n'.join('import '+b for b in blocks)+'\nimport F11All\nset_option autoImplicit false\nnamespace Polyomino57\n'
s+='theorem terminal_family_placed (row : List GridPoint) (h : FamilyMember row family11) : ∃ t, translate t row.toFinset ⊆ witness := by\n  exact '+elim(blocks)+'\nend Polyomino57\n'
(W/'TerminalFamilyPlaced.lean').write_text(s);mods.append('TerminalFamilyPlaced');(L/'terminal-aggregation-modules.json').write_text(json.dumps(mods,indent=2))
