from pathlib import Path
import re,sys,shutil
L=Path(__file__).resolve().parent
f=L/sys.argv[1];log=L/'logs'/(f.stem+'.log');s=log.read_text();src=f.read_text().splitlines()
attempt=L/'attempts'/f.stem;attempt.mkdir(parents=True,exist_ok=True);k=len(list(attempt.glob('*.lean')))
shutil.copyfile(f,attempt/f'{k}.lean')
for ext in ['log','guard.json','console']:
 p=L/'logs'/(f.stem+'.'+ext)
 if p.exists():shutil.copyfile(p,attempt/f'{k}.{ext}')
errors=list(re.finditer(r'^'+re.escape(f.name)+r':(\d+):\d+: error: ([^\n]+)',s,re.M))
if not errors or any('No goals to be solved' not in m[2] and 'This simp argument is unused:' not in m[2] for m in errors):print('nontrivial failure preserved',f.name);sys.exit(1)
for m in errors:
 if 'This simp argument is unused:' in m[2]:
  arg=s[m.end():].splitlines()[1].strip();idx=int(m[1])-1
  old=src[idx];src[idx]=src[idx].replace(', '+arg, '').replace(arg+', ', '').replace('['+arg+']','[]')
  assert old!=src[idx],(f,idx,arg)
remove={int(m[1])-1 for m in errors if 'No goals' in m[2]}
assert all(src[i].strip() in ['omega','tauto'] for i in remove)
f.write_text('\n'.join(s for i,s in enumerate(src) if i not in remove)+'\n')
print('removed solved-goal tactics',f.name,len(remove))
