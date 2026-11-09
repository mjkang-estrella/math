import pathlib,zipfile,os,subprocess,sys,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];Z=D/'dprime-source.zip'
with zipfile.ZipFile(Z,'w',zipfile.ZIP_DEFLATED) as z:
 for n in ['DPrime.lean','DPrimeAudit.lean']:z.write(D/'lean'/n,n)
F=D/'dprime-fresh-extracted';F.mkdir(exist_ok=False)
with zipfile.ZipFile(Z) as z:
 for n in z.namelist():
  assert n in ['DPrime.lean','DPrimeAudit.lean'];(F/n).write_bytes(z.read(n))
 assert all(not p.name.endswith('.olean') for p in F.iterdir())
os.environ['REPLAY_DIR']=str(F)
for label,args in [('dprime-fresh-build',['-o','DPrime.olean','DPrime.lean']),('dprime-fresh-audit',['DPrimeAudit.lean'])]:
 r=subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),label,sys.executable,'-I',str(D/'scripts/lean-run.py'),*args]);assert r.returncode==0
 r=json.loads((D/'logs'/f'{label}.receipt.json').read_text());assert r['returncode']==0
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');BIN=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
os.environ['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir() if p.is_dir())+':'+str(F);os.environ['PATH']=str(BIN)+':'+os.environ['PATH'];os.chdir(F)
subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),'dprime-fresh-leanchecker',str(BIN/'leanchecker'),'DPrime'],check=True)
r=json.loads((D/'logs/dprime-fresh-leanchecker.receipt.json').read_text());assert r['returncode']==0
out=dict(status='PASS',mathematical_module_declarations=43,packet_sha256=hashlib.sha256(Z.read_bytes()).hexdigest(),lean_version='4.34.1',mathlib_pin='d13f23b723b8a846827a245b89c10fc7d3f11612',trust_limits='Prebuilt dependency oleans trusted; no upstream source-to-olean attestation; leanchecker uses same kernel installation; sampled RSS only; no independent review or root acceptance.')
(D/'outputs/dprime-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
