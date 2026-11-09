import pathlib,zipfile,os,subprocess,sys,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];Z=D/'nonchalant-source.zip'
with zipfile.ZipFile(Z,'w',zipfile.ZIP_DEFLATED) as z:
 for n in ['Nonchalant.lean','Audit.lean']:z.write(D/'lean'/n,n)
F=D/'fresh-extracted';F.mkdir(exist_ok=False)
with zipfile.ZipFile(Z) as z:
 for n in z.namelist():
  assert n in ['Nonchalant.lean','Audit.lean'];(F/n).write_bytes(z.read(n))
 assert all(not p.name.endswith('.olean') for p in F.iterdir())
os.environ['REPLAY_DIR']=str(F)
for label,args in [('fresh-build',['-o','Nonchalant.olean','Nonchalant.lean']),('fresh-audit',['Audit.lean'])]:
 r=subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),label,sys.executable,'-I',str(D/'scripts/lean-run.py'),*args]);assert r.returncode==0
 r=json.loads((D/'logs'/f'{label}.receipt.json').read_text());assert r['returncode']==0
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');BIN=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
os.environ['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in P.iterdir() if p.is_dir())+':'+str(F);os.environ['PATH']=str(BIN)+':'+os.environ['PATH'];os.chdir(F)
subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),'fresh-leanchecker',str(BIN/'leanchecker'),'Nonchalant'],check=True)
r=json.loads((D/'logs/fresh-leanchecker.receipt.json').read_text());assert r['returncode']==0
out=dict(status='PASS',mathematical_module_declarations=68,packet_sha256=hashlib.sha256(Z.read_bytes()).hexdigest(),lean_version='4.34.1',mathlib_pin='d13f23b723b8a846827a245b89c10fc7d3f11612',trust_limits='Prebuilt dependency oleans trusted; no upstream source-to-olean attestation; leanchecker uses same kernel installation; sampled RSS only; no independent review or root acceptance.')
(D/'outputs/replay.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
