import hashlib,json,subprocess,sys
from pathlib import Path
current=sorted(Path('logs').glob('*seal_r3.log'))[-1]
excluded=['SHA256-MANIFEST.json',str(current),'receipt/'+current.stem+'.json']
files=sorted(p for p in Path('.').rglob('*') if p.is_file() and str(p) not in excluded)
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
s=json.dumps(dict(scope='PARTIAL_NOT_ACCEPTED_NO_ENDPOINT',credit=0,campaign_new=55,target=60,prior=39,terminal_noncircular_self_exclusions=excluded,sha256=hashes),indent=2)
subprocess.run([sys.executable,'-I','-B','write_lane.py','SHA256-MANIFEST.json'],input=s,text=True,check=True)
print('MANIFEST_FILES',len(hashes),'EXACT_EXCLUSIONS',excluded)
