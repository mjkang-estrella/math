from pathlib import Path
import hashlib,json,shutil,zipfile
R=Path(__file__).resolve().parent; L=R.parent; P=R/'packet'; P.mkdir(exist_ok=True)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
C=L/'sol-factorial-product-source-formal-r1'
freeze=json.loads((L/'root-factorial-product-formal-adoption-r1/component-freeze.json').read_text())
rows=[]
for n,h in freeze['files'].items():
 p=C/n; assert sha(p)==h,n; rows.append({'path':str(p),'sha256':h})
for lane, names in {
 'root-factorial-product-formal-adoption-r1':['DECISION.md','ROOT-REPLAY.json','component-freeze.json'],
 'root-factorial-product-review-freeze-r1':['ROOT-CHECK.md','ADOPTION.json','review-freeze.json'],
 'root-renyi-factorial-r116-adoption-r1':['DECISION.md'],
 'sol-factorial-product-preliminary-review-r1':['review.md','exact-receipt.json'],
 'sol-factorial-product-prior-clearance-r2':['review.md','exactcoverage.json','provenance.json','http.jsonl','primary-excerpt-provenance.json','candela-helfgott-excerpt.txt'],
}.items():
 for n in names:
  p=L/lane/n; dest=P/'evidence'/lane/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
  rows.append({'path':str(p),'sha256':sha(p)})
helper=L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
rows.append({'path':str(helper),'sha256':sha(helper)})
(R/'freeze-before.json').write_text(json.dumps(rows,indent=2)+'\n')
shutil.copyfile(helper,P/'helper_guard.py')
shutil.copyfile(C/'source-only.zip',P/'source-only.zip')
assert sha(P/'source-only.zip')=='3023e47a5994d0f4e0571c8fdf89b2b34a8ffb6f585636cd1eaf01026df1c055'
with zipfile.ZipFile(P/'source-only.zip') as z:z.extractall(P/'component')
for n in ['SUMMARY.md','PROVENANCE.md','FAILURES.md','pins.json']:
 shutil.copyfile(C/n,P/n)
(P/'README.md').write_text('''# Factorial product proof packet

Pending independent final review; credit 0. No acceptance or count change.
The author line follows the campaign convention "Research manuscript"; it asserts no invented human authorship.

The ordinary proof is paper.pdf; its editable source is paper.json and its deterministic builder is build_paper.py.
certificate.py regenerates all 176 integer valuation entries and checks exact rational products.
Both complete dissent-bearing reviews are retained under component/inputs and evidence/.
No survey inventories or own compiled Lean artifacts are packaged.

Use Python 3 with reportlab 4.4.3 and Poppler 24.02.0 (actual versions in build-environment.json).
All helpers must run under the unchanged helper_guard.py. From this directory:

    python helper_guard.py python certificate.py
    python helper_guard.py python build_paper.py
    python helper_guard.py python pack.py /absolute/new/packet.zip
    python helper_guard.py python component/replay.py source-only.zip /absolute/new/replay-directory

The strict original replay checks the pinned installed dependencies and historical frozen originals at their recorded paths.
For a self-contained provenance check without access to those historical originals, run:

    python helper_guard.py python portable_replay.py /absolute/new/replay-directory

This verifies every shipped component byte and all frozen copied inputs, the Lean binary, mathlib and eight pins,
upstream dependency artifacts including private/server hashes, then runs the unchanged Lean guard and exhaustive audit.
It does not claim to reverify unavailable historical originals. Only the portable orchestration differs; mathematical
source, FullAudit and the Lean guard are byte-identical. The strict replay receipt is separately retained by the lane.
Both replay modes compile one mathematical module and audit exactly 31 actual declarations with only the standard three axioms.
Pinned packages must be preinstalled at the exact paths in pins.json; neither replay downloads dependencies.
The Lean command is serial -j1 -M2700 with warningAsError, CPU210, wall230s, group RSS2800MiB at45ms.
The helper guard is AS/groupRSS512MiB CPU210 wall230s at40ms, BLAS1. Never raise caps.

To rebuild the outer archive byte-identically after extraction, run pack.py outside its input directory.
manifest.json verifies the full payload; the packer rejects unlisted files. Run compilation in a new external scratch
directory so generated .olean files cannot enter the payload. Historical failed logs remain in component/logs.
''')
print('frozen',len(rows),'originals; component copied unchanged')
