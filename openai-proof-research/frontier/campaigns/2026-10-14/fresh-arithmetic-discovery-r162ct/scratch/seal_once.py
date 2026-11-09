"""One-shot seal after the final verifier's same-logic preflight. No resealing."""
from pathlib import Path
import json, os, runpy
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct')
v=runpy.run_path(str(R/'verify.py'))
assert not (R/'MANIFEST.json').exists() and not (R/'REPORT.md').exists()
files,dirs=v['inventory'](R,{'MANIFEST.json','REPORT.md'})
m={'schema':1,'pin':v['PIN'],'files':files,'directories':dirs}
counts=v['check_payload'](R,m,{'MANIFEST.json','REPORT.md'})
v['check_bindings'](R,Path('.'))
fhash=v['digest']((R/'FINAL.md').read_bytes()); v['anchor'](R/'FINAL.md',fhash)
mb=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode(); mh=v['digest'](mb)
rb=('''# R162CT detached report

PREFREEZE/no nominee. No mathematical gates or count. Parent alone grades/counts.

Same-logic preflight MATCH: sorted safe exact membership, SHA256, lengths,
full file/directory stat modes, all11 pinned source blobs and4 Git trees,
complete preprints-tree anchor, five exact unchanged originals/copies, and
all eight downloaded primary PDF bindings. Tiny copied controls are recorded
in private/controls/RESULTS.json; originals restored and unchanged.

FINAL SHA256: %s
MANIFEST SHA256: %s

Payload: %d files, %d bytes. Directories including root: %d.
Whole-root files after sealing: %d. MANIFEST.json and this REPORT.md are the
two files outside the payload list. Their bytes are independently anchored.
No inherited manifest is used. After this one-shot seal, the packet is read-only.

Read-only check, using independent anchors from the handoff:
python verify.py --root <absolute-own-root> --final <FINAL-SHA256> \\
  --manifest <MANIFEST-SHA256> --report <REPORT-SHA256>

The local modular routing/reservoir comparison is paid; the all-q global
original-edge linear partition remains unproved/unfrozen. Full source reading,
119 primary semantic pages, partial ancestry and zero optional history traversals
are documented in FINAL.md and private/READING-LIMITS.md. Artifact integrity
is not mathematical correctness, novelty, acceptance or a campaign increment.
'''%(fhash,mh,counts[0],counts[2],counts[1],counts[0]+2)).encode()
rh=v['digest'](rb)
# All preflight operations above use the same core as the read-only verifier.
for name,data in [('MANIFEST.json',mb),('REPORT.md',rb)]:
 fd=os.open(R/name,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o644)
 with os.fdopen(fd,'wb') as f:
  os.fchmod(f.fileno(),0o644); f.write(data)
print(json.dumps({'FINAL':fhash,'MANIFEST':mh,'REPORT':rh,'payload_files':counts[0],'payload_bytes':counts[2],'directories':counts[1],'whole_root_files':counts[0]+2}))
