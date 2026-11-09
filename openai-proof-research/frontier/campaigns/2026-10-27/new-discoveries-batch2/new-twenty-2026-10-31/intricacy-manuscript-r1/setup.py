from pathlib import Path
import json,hashlib,shutil
r=Path(__file__).resolve().parent;b=r.parent;s=b/'intricacy-entropy-r5'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((r/'input-bindings.json').read_text());rows=[dict(path=p,expected=h,actual=digest(Path(p))) for p,h in x.items()];assert all(t['expected']==t['actual'] for t in rows)
(r/'integrity-before.json').write_text(json.dumps(rows,indent=2)+'\n')
for lane,files in [('candidate',[p.name for p in s.glob('*.lean')]+['proof-packet.zip','PROOF.md','SOURCE-MAPPING.md','SUMMARY.md','pins.json','lake-manifest.json','lean-toolchain','validate.py','replay.sh','manifest.json','source-hashes.json']),('fidelity-review',['REVIEW.md','SEMANTICS.md','review.json','complete-inventory.json','complete-inventory.log','strict-replay.json','provenance-and-static-checks.json','cached-source-receipt.json','clean/IndependentInventory.lean','independent-replay.py','inventory-run.py']),('source-review',['REVIEW.md','review.json','receipts.jsonl','source-hashes.json','registry-verification.json'])]:
 src={'candidate':s,'fidelity-review':b/'intricacy-fidelity-review-r1','source-review':b/'intricacy-source-review-r1'}[lane]
 for f in files:
  dest=r/'dossier'/lane/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src/f,dest)
for src in list((s/'inputs').glob('*'))+list((b/'intricacy-source-review-r1/sources').glob('*'))+list((b/'fresh-corpus-r13/sources').glob('*')):
 if src.is_file():
  dest=r/'dossier/sources'/src.parent.parent.name/src.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
for f in ['PROOF-333569.md','receipts.jsonl','source-search-notes.md','registry-reuse.json','access-limits.json']:
 dest=r/'dossier/fresh-context'/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(b/'fresh-corpus-r13'/f,dest)
shutil.copyfile(b/'intricacy-fidelity-review-r1/clean/IndependentInventory.lean',r/'dossier/IndependentInventory.lean')
print('prepared',len(rows))
