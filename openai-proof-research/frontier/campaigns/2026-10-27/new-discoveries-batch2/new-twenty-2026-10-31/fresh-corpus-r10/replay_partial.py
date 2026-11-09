from pathlib import Path
import os,subprocess,json,hashlib,datetime,zipfile,time
w=Path(__file__).parent.resolve();lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean');pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');env=os.environ.copy();env['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean') for p in sorted(pk.iterdir()))
files=['AutomatonCertificate.lean','PROOF-330264.md','FORMAL-GAPS.md','exact_spectra.py','exact_spectra.json','spectral_candidate.json','research-notes.md']
with zipfile.ZipFile(w/'330264-PARTIAL-certificate.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files:z.write(w/f,f)
x=w/'fresh-partial-extract';x.mkdir(exist_ok=True)
with zipfile.ZipFile(w/'330264-PARTIAL-certificate.zip') as z:z.extractall(x)
start=time.monotonic();r=subprocess.run([str(lean),'-j2','-M2300','-DwarningAsError=true','AutomatonCertificate.lean'],cwd=x,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
(x/'replay.log').write_text(r.stdout)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=r.returncode,elapsed_s=time.monotonic()-start,command=[str(lean),'-j2','-M2300','-DwarningAsError=true','AutomatonCertificate.lean'],scope='PARTIAL finite clique-automaton certificate ONLY. No full MathDB endpoint or spectral/normal-form proof.',axioms=r.stdout.strip(),lean_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',files_sha256={f:hashlib.sha256((x/f).read_bytes()).hexdigest() for f in files},packet_sha256=hashlib.sha256((w/'330264-PARTIAL-certificate.zip').read_bytes()).hexdigest())
# Hash exact read-only dependencies used by the imported list module, conservatively all built olean headers are not inferred.
receipt['dependency_scope']='mathlib source revision pinned; exact direct source and olean hashes below. Complete import-closure inventory not claimed for this partial packet.'
receipt['direct_dependency_hashes']={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [pk/'mathlib/Mathlib/Data/List/Basic.lean',pk/'mathlib/.lake/build/lib/lean/Mathlib/Data/List/Basic.olean']}
(w/'partial-replay-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps({k:receipt[k] for k in ['exit_code','elapsed_s','scope','axioms']},indent=2))
assert r.returncode==0 and 'sorryAx' not in r.stdout
