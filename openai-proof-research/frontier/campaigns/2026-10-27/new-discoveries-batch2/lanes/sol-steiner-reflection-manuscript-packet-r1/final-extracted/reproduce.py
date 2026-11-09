"""Verify final payload, rebuild PDF/ZIP identically, replay original source-only component."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY))
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
import hashlib,json,os,signal,subprocess,sys
from pathlib import Path
signal.alarm(230)
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=os.environ.copy()
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','BLIS_NUM_THREADS','NUMEXPR_NUM_THREADS']:env[k]='1'
manifest=json.loads((R/'packet-manifest.json').read_text())
for n,h in manifest.items():assert sha(R/n)==h,n
pins=json.loads((R/'component/pins.json').read_text());lean=Path(pins['lean_binary'])
assert sha(lean)==pins['lean_sha256']
version=subprocess.check_output([str(lean),'--version'],text=True,env=env).strip()
assert 'version 4.34.1' in version,version
pdf=sha(R/'paper.pdf')
subprocess.run([sys.executable,str(R/'build_pdf.py')],env=env,check=True,timeout=225)
assert sha(R/'paper.pdf')==pdf,'PDF rebuild drift'
subprocess.run([sys.executable,str(R/'package.py')],env=env,check=True,timeout=225)
# Compare the rebuilt archive with the caller-supplied final frozen archive.
if len(sys.argv)>2:assert sha(Path(sys.argv[2]).resolve())==sha(R/'steiner-final-review-packet.zip'),'ZIP rebuild drift'
component=R/'evidence/root-steiner-reflection-formal-replay-r1/steiner-source-component.zip'
dest=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else R/'verification-replay'
subprocess.run([sys.executable,str(R/'component/replay.py'),str(component),str(dest)],env=env,check=True,timeout=225)
r=json.loads((dest/'replay-receipt.json').read_text())
assert r['declaration_count']==118 and len(r['pins']['packages'])==9
assert (dest/'logs/OriginAudit.log').read_bytes()==(R/'evidence/root-steiner-reflection-formal-replay-r1/root-extracted/logs/OriginAudit.log').read_bytes()
for n,h in manifest.items():assert sha(R/n)==h,n
receipt={'status':'PASS','lean_version':version,'lean_binary_sha256':sha(lean),'pdf_byte_identical':True,'pdf_sha256':pdf,'zip_sha256':sha(R/'steiner-final-review-packet.zip'),'zip_byte_identical':len(sys.argv)>2,'source_only_initial_artifacts':0,'modules':6,'declarations':118,'nine_packages_asserted':True,'actual_audit_byte_identical_to_root':True,'actual_audit_sha256':sha(dest/'logs/OriginAudit.log'),'full_formal_receipt':str(dest/'replay-receipt.json'),'resource_note':'Inherited guard: RSS2800MiB sampled .045s, per Lean stage CPU210/wall230. Python AS soft512MiB; unlimited hard AS solely permits separate Lean launch policy. Upstream reused, not rebuilt.'}
(dest/'final-packet-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
