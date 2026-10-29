import hashlib, json, shutil, subprocess, sys
from pathlib import Path
from fractions import Fraction as Q
from datetime import datetime, timezone

here=Path(__file__).resolve().parent
batch=here.parent.parent
lane=batch/'lanes/sol-fresh-source-discovery-r62'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prov=json.loads((lane/'provenance.json').read_text())
rows=[]
for r in prov['http']:
    if 'sha256' in r and 'file' in r:
        p=lane/r['file']
        rows.append({'path':r['file'],'expected':r['sha256'],'actual':sha(p)})
assert rows and all(r['expected']==r['actual'] for r in rows)
inventory={str(p.relative_to(lane)):sha(p) for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
copy=here/'check-copy'
copy.mkdir(exist_ok=True)
shutil.copyfile(lane/'compact.py',copy/'compact.py')
with (here/'compact.log').open('w') as log:
    subprocess.run([sys.executable,'compact.py'],cwd=copy,stdout=log,stderr=subprocess.STDOUT,check=True)
assert (copy/'compact.json').read_bytes()==(lane/'compact.json').read_bytes()
# Arithmetic in the actual public function witness's final comparison.
assert Q(1672,1000)**2 * Q(31416,10000)**13 < 136700*69
assert Q(1,2)**12 <= 12*Q(1,2)**11
receipt={
 'utc':datetime.now(timezone.utc).isoformat(),
 'decision':'EXCLUDE_PRIOR; preserve equal-dimension variants without discovery credit',
 'credit':0,'counts':{'additional':7,'total':37},
 'source':'Kalmykov-Karp Analysis Mathematica43(2017)567-580 Conjectures1/2',
 'root_read':'Published text conjectures, actual public claim definitions and endpoint proofs for coefficient/function/two-block assertions; selected function witness estimates and proof; no fresh download or complete dependency audit.',
 'scope_bridge':'FunctionResult has p=1,q=12,a=(1),b=(1/2)^12,mu=1,alpha=beta=1/2,x=2000 and strictly negative convergent-series Turanian. Empty unshifted blocks specialize Conjecture2 to the same function. TwoBlockResult also gives a nonempty shifted-numerator coefficient counterexample. This is positive matching-body evidence, not a registry badge or absence inference.',
 'root_validation':'Compact equal-dimension arithmetic certificate replay PASS, identical JSON; actual public witness final rational comparison and symmetric-condition arithmetic PASS.',
 'full_worker_suites_rerun_by_root':False,
 'formal_claim':'No root Lean replay or new formal PASS; external dependency closure not audited.',
 'limits':['Current registry freshness HOLD; immutable latest-observed revision is not current HEAD.','No new priority claim for the equal-dimension variant.','Worker registry screen was later than requested; missed early-screen protocol preserved.','No full root review of the uncredited infinite-tail variant is asserted.'],
 'source_hashes_verified':rows,'lane_inventory':inventory,
}
(here/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
assert inventory=={str(p.relative_to(lane)):sha(p) for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
nextp=batch/'NEXT.md'
s=nextp.read_text().replace('Three fresh Sol high/default research lanes r65 finite structures, r62 analysis,\nr64 arithmetic/algebra are active; no children.', 'r62 Kalmykov-Karp gamma-shift variants are excluded by actual public proofs of\nthe same universal source claims; see lanes/root-fresh-source-r62-handback/ADOPTION.json.\nThree fresh Sol high/default research lanes r65 finite structures, r66 analysis,\nr64 arithmetic/algebra are active; no children.')
nextp.write_text(s)
paths=[str(nextp.relative_to(Path.cwd()))]
paths += [str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='pathspec.txt']
(here/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'checks':'PASS','http_hashes':len(rows),'lane_files_unchanged':len(inventory),'counts':[7,37]}))
