from pathlib import Path
import json,hashlib,subprocess,sys,datetime
R=Path(__file__).resolve().parent
spec={'foliations':[(1,115),(909,943)],'matroid':[(1,155),(628,680),(2630,2725)],'ellipsoids':[(155,225),(3154,3208),(3656,3708)],'integer-homology':[(1,100),(376,495)],'percolation':[(1,120),(1009,1085)]}
out=[]
for name,ranges in spec.items():
 lines=(R/f'sources/{name}.txt').read_text().splitlines(keepends=True)
 for a,b in ranges:out.append({'file':f'sources/{name}.txt','first_line':a,'last_line':b,'excerpt':''.join(lines[a-1:b])})
(R/'successor-excerpts.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
files=[]
for p in sorted(R.rglob('*')):
 if not p.is_file():continue
 n=str(p.relative_to(R))
 if n in {'manifest.json','final-receipt.json'}:continue
 b=p.read_bytes();files.append({'path':n,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(R/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(R/'verify.py')],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256((R/'manifest.json').read_bytes()).hexdigest(),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'guard':'helper_guard.py fixed512MiB AS/groupRSS CPU210s wall230s; seal and read-only verifier run within guarded process group','scope':'50 assigned statements only; zero proposals; counts9/39/40 unchanged'}
(R/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
