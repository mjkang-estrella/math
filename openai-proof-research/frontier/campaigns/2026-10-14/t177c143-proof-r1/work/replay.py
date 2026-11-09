from pathlib import Path
import subprocess,sys,os,hashlib,json,shutil,datetime
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/t177c143-proof-r1'
A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
C=R/'packet/private/incoming-author'
O=R/'packet/private/replay';O.mkdir(parents=True,exist_ok=True)
def snap(root):return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}
before=snap(A);copy_before=snap(C)
env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(R/'work')}
anchor=json.loads((R/'packet/private/incoming-observation.json').read_text())['external_anchors']
cmd=[sys.executable,str(C/'packet/public/verify.py'),str(C)]
for n,flag in [('FINAL.json','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:cmd.extend([flag,anchor[n]])
cases=[]
def run(name,cmd,timeout=60):
 p=subprocess.run(cmd,capture_output=True,text=True,env=env,cwd=R/'work',timeout=timeout)
 (O/(name+'.stdout')).write_text(p.stdout);(O/(name+'.stderr')).write_text(p.stderr)
 cases.append({'case':name,'returncode':p.returncode,'command':cmd})
 assert p.returncode==0,(name,p.stderr,p.stdout)
run('incoming-exact-verifier',cmd)
assert snap(C)==copy_before,'copied verifier changed copy'
D=R/'work/disposable-controls';(D/'work').mkdir(parents=True,exist_ok=True)
(D/'packet/public').mkdir(parents=True,exist_ok=True)
shutil.copy2(C/'work/run_controls.py',D/'work/run_controls.py')
shutil.copy2(C/'packet/public/verify.py',D/'packet/public/verify.py')
run('copied-seven-controls',[sys.executable,str(D/'work/run_controls.py')])
Q=R/'work/disposable-diagnostic';Q.mkdir(exist_ok=True)
shutil.copy2(C/'packet/public/check_coherent.py',Q/'check_coherent.py')
run('copied-finite-diagnostic',[sys.executable,str(Q/'check_coherent.py')],90)
assert snap(A)==before,'original changed during replay observation'
(O/'receipt.json').write_text(json.dumps({'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cases':cases,'incoming_files_before_after_equal':True,'incoming_copy_unchanged_by_verifier':True,'original_code_executed':False,'meaning':'Only disposable copies executed after code reading. run_controls writes its miniature fixture under disposable-controls only. Artifact and finite diagnostic checks are not mathematical gates.'},indent=2)+'\n')
print(json.dumps({'cases':cases,'original_before_after_equal':True},indent=2))
