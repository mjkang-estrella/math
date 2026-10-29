from pathlib import Path
import subprocess,shutil,json
L=Path(__file__).resolve().parent
# Invoked only once the immutable strict replay has exited successfully.
assert json.loads((L/'closure/verification/receipt.json').read_text())['strict']
q=subprocess.run(['python3',str(L/'bench/build.py')]);assert q.returncode==0
q=subprocess.run(['python3',str(L/'bench/large.py')]);assert q.returncode==0
W=L/'bench/work'
shutil.copyfile(L/'formal/FamilyAssembly.lean',W/'FamilyAssembly.lean')
q=subprocess.run(['python3',str(L/'bench/run.py'),'-o','FamilyAssembly.olean','FamilyAssembly.lean'],cwd=W,capture_output=True,text=True)
(L/'bench/FamilyAssembly.log').write_text(q.stdout+q.stderr);print('FamilyAssembly',q.returncode,flush=True)
