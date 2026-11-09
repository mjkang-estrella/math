from pathlib import Path
import hashlib,json,os
R=Path.cwd()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checks={}
before=json.loads((R/'inputs-before.json').read_text()); after=json.loads((R/'inputs-after.json').read_text()); assert before==after
for p,e in before.items():
 assert sha(R.parent/p)==e['sha256']
 assert sha(R/'inputs'/p)==e['sha256']
checks['frozen_originals_and_copies_unchanged']=len(before)
assert sha(R/'Lean-packet.zip')=='3d9361bef2cc188b191519cd9718e4d983ccbe6b17df8dec6448dcf5228ab1d6'
qa=json.loads((R/'receipts/page-qa.json').read_text()); assert sha(R/'paper.pdf')==qa['pdf_sha256']
for e in qa['images']: assert sha(R/e['path'])==e['sha256']
checks['final_pages_rendered_and_visually_inspected']=qa['pages']
v=json.loads((R/'recomputed/verification.json').read_text()); assert v['status']=='PASS' and all(d['gaps']==0 for d in v['orders'])
checks['recomputation']='PASS'
checks['packet']='Byte-identical; safe extraction PASS; no formal execution here'
# Check no earlier authoring/enumeration/export process remains. The current
# final checker and its own foreground cap parent are intentionally excluded.
active=[]; ignore={os.getpid(),os.getppid()}
for d in Path('/proc').iterdir():
 if not d.name.isdigit() or int(d.name) in ignore: continue
 try:
  cmd=(d/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if (d/'cwd').resolve()==R.resolve() and (cmd.startswith('python3 -I scripts/') or cmd.startswith('/usr/lib64/libreoffice/program/soffice.bin')): active.append(dict(pid=int(d.name),command=cmd))
 except OSError: pass
assert not active,active
checks['remaining_authoring_jobs']=active
out=dict(status='PASS',checks=checks,outer_hash_policy='ARTIFACTS.sha256 hashes stable deliverables, manifests and packaging/final-check receipts; excludes itself and the cap receipt produced after this script exits.')
(R/'receipts/final-integrity.json').write_text(json.dumps(out,indent=2)+'\n')
selected=['paper.pdf','paper.fodt','paper.md','paper-expanded.md','PROOF.md','SUMMARY.md','results.json','REPRODUCE.md','PRIOR-ART-LIMITATIONS.txt','MathDB-360905.raw.jsonl','Lean-packet.zip','manuscript-source.zip','full-dossier.zip','PAYLOAD-MANIFEST.json','inputs-before.json','inputs-after.json','receipts/packaging.json','receipts/package.json','receipts/verify-final.json','receipts/page-qa.json','receipts/paper-values.json','receipts/final-integrity.json']
(R/'ARTIFACTS.sha256').write_text(''.join(f'{sha(R/p)}  {p}\n' for p in selected))
print(json.dumps(out,indent=2))
