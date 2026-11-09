from pathlib import Path
import hashlib,json,subprocess,sys
p=Path.cwd()
excluded=['manifest.json','terminal_seal.receipt.json','terminal_seal.output.txt']
files=[]
for f in sorted(p.rglob('*')):
 if f.is_file():
  rel=str(f.relative_to(p))
  if rel in excluded:continue
  b=f.read_bytes();files.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
receipts=[]
for row in files:
 if row['path'].endswith('.receipt.json'):
  d=json.loads((p/row['path']).read_text());receipts.append({'path':row['path'],'exit':d.get('exit'),'killed':d.get('killed'),'sampled_group_rss_peak_bytes':d.get('sampled_group_rss_peak_bytes'),'wall_s':d.get('wall_s')})
assert json.loads((p/'frozen-after.json').read_text())['mismatches']==[]
m={'kind':'exhaustive own-lane byte manifest at terminal seal','files':files,'file_count':len(files),'completed_runner_receipts':receipts,'terminal_noncircular_self_exclusions':{'manifest.json':'self hash would be circular','terminal_seal.receipt.json':'runner writes its terminal receipt after this script returns','terminal_seal.output.txt':'runner writes its terminal output after this script returns'},'no_later_frozen_writes':True,'credit':0,'campaign':'57/60 beyond39 prior,96 total unchanged'}
r=subprocess.run([sys.executable,'-I','-B',str(p/'write_lane.py'),'manifest.json'],input=json.dumps(m,indent=2)+'\n',text=True,capture_output=True);assert r.returncode==0,r.stderr
for row in files:
 b=(p/row['path']).read_bytes();assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256'],row['path']
print(json.dumps({'sealed_files':len(files),'completed_receipts':len(receipts),'manifest_sha256':hashlib.sha256((p/'manifest.json').read_bytes()).hexdigest(),'exclusions':excluded,'credit':0}))
