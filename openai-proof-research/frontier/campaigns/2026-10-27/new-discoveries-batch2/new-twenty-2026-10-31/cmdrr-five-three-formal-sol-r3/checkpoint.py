import hashlib,json,subprocess,sys
from pathlib import Path
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=[]
for p in sorted(Path('receipt').glob('*.json')):
 a=json.loads(p.read_text());r.append(dict(path=str(p),sha256=sha(p),exit=a['exit'],label=a['label'],group_members_left=a['group_members_left']))
mods=[]
for p in sorted(Path('src').glob('*.lean')):
 o=Path('build')/(p.stem+'.olean'); matches=[a for a in r if a['label']=='lean_'+p.stem];latest=matches[-1] if matches else None
 mods.append(dict(module=p.stem,source_sha256=sha(p),olean_sha256=sha(o) if o.exists() else None,latest_strict=latest))
s=json.dumps(dict(status='PARTIAL_NO_ENDPOINT',credit=0,campaign=55,target=60,previous=39,modules=mods,receipts=r,unpaid=["A+B=1+z actual occurrence incidence sums","B+z=2, arbitrary two-cycle orientation bridge and single-row3+2 elimination","Single-row five-cycle classification","Full swapped-source column correspondence/classification","Cycle/support signs, T sign and contradiction","Canonical noSource and universal ExistsFiveThree negation","Final endpoint audits, substantive controls, finished paper/PDF/visual QA, independent review"],deviations=['Initial inventory omitted lane cwd and was interrupted before listing display; metadata traversal outside lane cannot be excluded. No proof/source bytes from other lanes displayed. Interrupted runner has no normal receipt.','runner --help failed IndexError','tee /dev/tty display attempt exit1 because runner session has no controlling tty','Inherited deviations retained in inputs/previous/results/326555.json']),indent=2)
subprocess.run([sys.executable,'-I','-B','write_lane.py','results/326555.json'],input=s,text=True,check=True)
