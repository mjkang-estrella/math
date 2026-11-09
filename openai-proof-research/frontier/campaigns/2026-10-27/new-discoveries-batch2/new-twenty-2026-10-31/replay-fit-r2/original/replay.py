from pathlib import Path
import subprocess,sys,json,hashlib,time,re,datetime,os
w=Path(__file__).resolve().parent
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
order=['GroupSemantics','NormalForm','TraceAction','AutomatonSemantics','WordCounting','MachineInvariant','SpectralDefinitions','ConcreteMachine','SpectralWitness','Endpoint']
allowed={'propext','Classical.choice','Quot.sound'}
manifest=json.loads((w/'packet-manifest.json').read_text())
for p,h in manifest['files'].items():
 assert hashlib.sha256((w/p).read_bytes()).hexdigest()==h, p
start=time.monotonic();receipts=[];audits=[]
for name in order:
 print('BUILD',name,flush=True)
 r=subprocess.run([sys.executable,str(w/'check.py'),name+'.lean'],cwd=w,capture_output=True,text=True,timeout=320)
 print(r.stdout+r.stderr,flush=True)
 rc=json.loads((w/(name+'.lean.receipt.json')).read_text());receipts.append(rc)
 if r.returncode:sys.exit(r.returncode)
 for decl,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout):
  ax=[a.strip() for a in axioms.split(',') if a.strip()]
  assert set(ax)<=allowed,(decl,ax)
  audits.append(dict(declaration=decl,axioms=ax))
assert any(a['declaration']=='MathDB330264.conjecture_false' for a in audits)
receipt=dict(status='PASS_FULL_LEAN_ENDPOINT',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed=time.monotonic()-start,builds=receipts,axiom_audits=audits,lean_binary_sha256=hashlib.sha256(Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean').read_bytes()).hexdigest(),mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',source_hashes={n+'.lean':hashlib.sha256((w/(n+'.lean')).read_bytes()).hexdigest() for n in order},credit=0,acceptance='independent fidelity and novelty/significance reviews and paper remain root work')
(w/'replay-receipt.json').write_text(json.dumps(receipt,indent=2))
print(receipt['status'],receipt['elapsed'],flush=True)
