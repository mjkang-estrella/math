from pathlib import Path
import json,hashlib,zipfile,subprocess,datetime
p=Path(__file__).parent.resolve();sha=lambda b:hashlib.sha256(b).hexdigest();formal=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
env={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_binary':str(lean),'lean_sha256':sha(lean.read_bytes()),'version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'package_manifest':str(formal/'lake-manifest.json'),'package_manifest_sha256':sha((formal/'lake-manifest.json').read_bytes()),'packages':json.loads((formal/'lake-manifest.json').read_text())['packages'],'trust':'Read-only external cached oleans trusted; no full upstream rebuild or source-to-olean attestation. 6 GiB sampled RSS limit; 12 GiB virtual limit; 120 CPU seconds; 140 wall seconds; two CPUs; 50 ms sampling may miss transients.'};(p/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
files=['Game.lean','run-lean.py','environment.json']
with zipfile.ZipFile(p/'355140-proof-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for name in files:z.write(p/name,name)
replay=p/'fresh-replay';replay.mkdir(exist_ok=True)
with zipfile.ZipFile(p/'355140-proof-source.zip') as z:
 assert all('/' not in n and '..' not in n for n in z.namelist());z.extractall(replay)
assert not list(replay.glob('*.olean'))
r=subprocess.run(['python',str(replay/'run-lean.py')],capture_output=True,text=True,timeout=150);(p/'fresh-replay.log').write_text(r.stdout+r.stderr);rec=json.loads((replay/'lean-receipt.json').read_text());rec['extraction_source_only']=True;rec['packet_sha256']=sha((p/'355140-proof-source.zip').read_bytes());rec['same_source']=sha((replay/'Game.lean').read_bytes())==sha((p/'Game.lean').read_bytes());(p/'fresh-replay-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2));assert rec['exit']==0
