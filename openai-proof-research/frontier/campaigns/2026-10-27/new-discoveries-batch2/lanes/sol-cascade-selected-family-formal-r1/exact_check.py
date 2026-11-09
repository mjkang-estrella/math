from pathlib import Path
import os,resource,json,hashlib,re,time
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,)*2)
b=Path(__file__).resolve().parent
start=time.monotonic()
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while c:=f.read(1024*1024):h.update(c)
 return h.hexdigest()
frozen=json.loads((b/'frozen-before.json').read_text())
after={p:sha(p) for p in frozen};assert frozen==after
(b/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
for n in ['DepthDefs.lean','SourceDefs.lean','TreeConstruction.lean','DepthArithmetic.lean','DepthAnalysis.lean','run_lean.py']:
 p=next(Path(p) for p in frozen if Path(p).name==n)
 assert sha(p)==sha(b/'formal'/n)==sha(b/'replay/formal'/n)
lean='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
assert sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
receipts=json.loads((b/'replay/verification/receipt.json').read_text())
assert len(receipts)==8 and all(r['exit']==0 and r['peakRSS']<3*1024**3 and r['seconds']<180 for r in receipts)
names=json.loads((b/'declarations.json').read_text()); audit=(b/'replay/verification/Audit.log').read_text()
observed={}
for n in names:
 m=re.search(re.escape("'"+n+"'")+r' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])',audit)
 assert m,n
 axioms=[] if m[2] is None else [re.sub(r'\.\{[^}]*\}','',s.strip()) for s in m[2].split(',')]
 assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(n,axioms)
 observed[n]=axioms
for p in (b/'formal').glob('*.lean'):
 assert sha(p)==sha(b/'replay/formal'/p.name)
 assert not re.search(r'\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b',p.read_text(),re.M),p
(b/'audit-results.json').write_text(json.dumps(observed,indent=2)+'\n')
(b/'checks.json').write_text(json.dumps({'status':'PASS','diagnostic_role':'integrity, inventory and receipt bookkeeping only; no finite mathematical test substitutes for proof','limits':{'AS_bytes':512*1024**2,'CPU_seconds':25,'BLAS_threads':1},'frozen_files':len(frozen),'audited_declarations_including_8_fields':len(names),'lean_sha256':sha(lean),'seconds':time.monotonic()-start},indent=2)+'\n')
print((b/'checks.json').read_text())
