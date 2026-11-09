from pathlib import Path
import subprocess,sys,zipfile,json,hashlib
L=Path(__file__).resolve().parent
q=subprocess.run(['python3','package_complete.py'],cwd=L);assert q.returncode==0
D=L/'fresh-extracted';D.mkdir()
with zipfile.ZipFile(L/'source-only-complete-r5.zip') as z:z.extractall(D)
q=subprocess.run(['python3','fresh_replay.py'],cwd=D)
if q.returncode:sys.exit(q.returncode)
r=json.loads((D/'verification/receipt.json').read_text());assert r['status']=='PASS_CLOSED_ENDPOINT'
(L/'FINAL-RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n')
summary='''# Closed proof construction; root owns acceptance

The literal unconditional `Polyomino57.UniversalContainer 11 Polyomino57.witness`, `¬ Polyomino57.SourceFormula`, and `Polyomino57.minimumSize 11 ≤ 57` compile and pass a fresh source-only extracted replay. See `CompleteEndpoint.lean` inside the deterministic source packet and `fresh-extracted/verification/declaration-inventory.json` for actual types, axioms, origins and flags.

Every source leaf in stages7–10 is covered by a closed universal closure theorem. Each row proof checks the full successorFastRowCheck on its row-local target array and proves every target's exact leaf index in the common balanced family. Stage theorems traverse the actual source trees; no expected row count is a premise. The size7 family is kernel-linked to the existing layer7, whose normalized coverage is reused.

Each terminal source leaf is covered by a closed placement theorem. Each row proof uses actual frozen terminal-chunk membership at its supplied index, the checked placement-tree leaf, and kernel-checked equality of translated coordinate finsets. Raw negative coordinates and different anchoring are handled by those exact equalities and the existing normalization-transfer theorem. No D4 transformations or weaker source claim occur.

Development reused r4 component oleans; the delivered fresh replay consumed none of them. The source packet includes every transitive candidate dependency, every consumed frozen terminal shard and split actual-origin audit modules. Standard three axioms only. Inherited partial compiler helper declarations are included in the inventory; their actual unsafe/axiom flags are false. No new unsafe declarations or axioms were introduced.

Failures and resource receipts are retained in this lane. Generator scripts enforce 512MiB address-space bounds; Lean is spawned before its supervisor takes that bound, with serial-j1, warningAsError, autoImplicit=false, CPU210sec, wall230sec, 45ms process-group RSS samples and kill threshold2800MiB. Caps were not raised. The serial coordinator itself must launch separately capped children and consequently does not inherit a hard AS bound into Lean.

Worker credit0; counts5additional/35total. Root owns manuscript, review and acceptance. No git operations, children, browser actions, external messages, uploads or account actions were used.
'''
(L/'SUMMARY.md').write_text(summary);(L/'HANDOFF.md').write_text(summary+'\nArchive and replay measurements:\n\n'+json.dumps(json.loads((L/'archive.json').read_text()),indent=2)+'\n\n'+json.dumps(r,indent=2)+'\n')
print('FINAL FRESH CLOSED PROOF PASS',flush=True)
