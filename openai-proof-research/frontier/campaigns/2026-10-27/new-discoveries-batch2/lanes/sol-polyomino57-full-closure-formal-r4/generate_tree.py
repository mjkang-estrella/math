from pathlib import Path
import json,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;D=L/'tree';D.mkdir(exist_ok=True)
rows=[json.loads(s) for s in (L/'data/layer11.jsonl').read_text().splitlines()]
cells=lambda P:'['+','.join('(%d,%d)'%tuple(p) for p in P)+']'
def balanced(names):
 if len(names)==1:return names[0]
 m=len(names)//2;return '(.branch '+balanced(names[:m])+' '+balanced(names[m:])+')'
mods=[]
for start in range(0,len(rows),2048):
 nm='TreeBlock%03d'%(start//2048);mods.append(nm)
 s=['import FamilyTree','set_option autoImplicit false','set_option maxRecDepth 65536','set_option maxHeartbeats 10000000','namespace Polyomino57'];leaves=[]
 for k in range(start,min(start+2048,len(rows)),32):
  leaf=nm+'L%d'%((k-start)//32);leaves.append(leaf)
  s+=['def '+leaf+' : RowFamilyTree := .leaf #['+','.join(cells(P) for P in rows[k:min(k+32,start+2048)])+']']
 s+=['def '+nm+' : RowFamilyTree := '+balanced(leaves),'end Polyomino57'];(D/(nm+'.lean')).write_text('\n'.join(s)+'\n')
(D/'TreeAll.lean').write_text('\n'.join('import '+m for m in mods)+'\nset_option autoImplicit false\nnamespace Polyomino57\ndef terminalRowTree : RowFamilyTree := '+balanced(mods)+'\nend Polyomino57\n')
(D/'modules.json').write_text(json.dumps(mods+['TreeAll'],indent=2))
