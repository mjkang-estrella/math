import pathlib,json,hashlib,zipfile,subprocess,os
R=pathlib.Path(__file__).resolve().parent
p=R/'runlean.py';s=p.read_text().replace("env=os.environ.copy();env['LEAN_PATH']", "env={'PATH':'/usr/bin:/bin','LC_ALL':'C.UTF-8'};env['LEAN_PATH']");p.write_text(s)
paths=[pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'),pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json')]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(R/'environment.json').write_text(json.dumps({'bindings':{str(p):h(p) for p in paths},'lean_version':subprocess.check_output([str(paths[0]),'--version'],text=True).strip(),'mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','limits':'2 CPU affinity, Lean -j2;12GiB address space;110 CPU seconds;120s wall per Lean call; AS cap includes mappings, not aggregate RSS guarantee','cache_trust':'prebuilt external oleans trusted; no full upstream rebuild or source-to-olean attestation','sanitized_env':['PATH','LC_ALL','LEAN_PATH'],'early_failed_runs':'6GiB address space caused import-read error; default thread pool hit thread cap; subsequent limited -j2 and12GiB replay succeeds'},indent=2)+'\n')
with zipfile.ZipFile(R/'proof-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in ['Taylor.lean','Audit.lean','runlean.py','environment.json']:z.write(R/f,f)
fresh=R/'fresh-extracted';fresh.mkdir(exist_ok=True)
with zipfile.ZipFile(R/'proof-source.zip') as z:z.extractall(fresh)
logs=[]
for args in [['-o','Taylor.olean','Taylor.lean'],['Audit.lean']]:
 p=subprocess.run(['/usr/bin/python3',str(fresh/'runlean.py'),*args],capture_output=True,text=True,timeout=130);logs.append(p.stdout+p.stderr);print(logs[-1],flush=True);assert p.returncode==0
(R/'fresh-replay.log').write_text('\n'.join(logs))
