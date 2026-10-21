#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,os,stat,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153').resolve();names={'FINAL.md','MANIFEST.json','REPORT.md'}
assert not any((R/n).exists() for n in names),'One final seal only'
files=[]
for base,dirs,ns in os.walk(R,topdown=True,followlinks=False):
 for n in dirs:assert not (Path(base)/n).is_symlink()
 for n in ns:
  p=Path(base)/n;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
  files.append({'path':str(p.relative_to(R)),'bytes':s.st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
files.sort(key=lambda x:x['path'])
m={'format':1,'scope':'exact selected regular single-link payload files; no inherited original manifest','outside_envelopes':sorted(names),'limits':'Does not bind empty directories, modes or original archive membership. Artifact verification is not a mathematical gate.','files':files}
(R/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
msha=hashlib.sha256((R/'MANIFEST.json').read_bytes()).hexdigest()
(R/'FINAL.md').write_text(f'''# PREFREEZE / no nominee — analytic r153

Authorized Codex / GPT-6 Astra / high / default service tier. Pin and operative proofs stipulated true. Parent-owned campaign19/20, latestR041, unchanged. No frozen theorem, submitted full author proof, independent grade or count.

Source348 was developed through a stronger source/classical reduction: on smooth closed connected four-manifolds with nonzero Euler characteristic, small critical trace-free Ricci and negative-sectional energies force positive Yamabe sign and uniform initial geometry. Ge–Wang's actual conformal proof, the dimension-four negative-scalar energy identity, and EG's full tail/smoothing proof account for the remaining interfaces, including arbitrary initial scalar sign and the base quotient. No identifiable nonroutine operation remains in this calculation, and none is nominated. See DERIVATION.md and notes/YAMABE-AND-SCALAR.md.

The earlier Bochner and finite-cover difficulties are paid; they are not preserved as gaps. No claim for arbitrary chi=0, original-distance rates, dynamical attraction, optimal constants, worldwide priority or exhaustive literature/history coverage. The exact shrinking-circle and rotational-neck checks are in notes/GEOMETRIC-CHECKS.md. All old scopes and dispositions remain unchanged.

Material procedural defects: a catalogue-boundary bug emitted a truncated whole map, violating the family-screen limit. Broad history filtering also admitted TEN-FINDINGS and administrative derivatives. No active peer premise was used. Coarse omissions, opaque aliases, partial companion/transitive reads, truncations and late copies are disclosed in READING-LIMITS.md, ISOLATION.md and notes/INCIDENTS.md. This is not a clean-isolation certificate.

Manifest payload: {len(files)} files. Exactly three root-level envelopes are outside it: FINAL.md, MANIFEST.json, REPORT.md. Manifest SHA256: {msha}. All three detached hashes must be obtained independently and passed to tools/verify.py. Private source/primary/history/search/extract/render/copy/control bodies retain original rights. No downstream work.
''')
(R/'REPORT.md').write_text(f'''# Outside report envelope — r153

Outcome: PREFREEZE/no nominee. Parent alone integrates/reviews/counts. The strongest integrated reduction and limits are in DERIVATION.md, GAPS.md and the notes. This report assigns no mathematical gate.

Exactly {len(files)} payload files are bound by MANIFEST.json, SHA256 {msha}; the three outside root-level envelopes are FINAL.md, MANIFEST.json and this REPORT.md. Incoming-original identities are separate from selected-copy membership. The manifest binds file membership and bytes, not modes or empty directories.

Authentication reproduced27 canonical objects totaling356730 bytes against the complete13223-entry tree, exact pin paths, sizes, Git blobs and SHA256. Eleven selected original copies still matched their unchanged originals. Primary originals, selected members and render/extraction derivatives have separate recorded identities.

The proportionate copied control has two selected members with its own exact manifest and anchors; it is not a whole-original packet. Baseline and restoration accepted. Changed payload, missing payload, hidden extra and wrong report anchor rejected. Every verification preserved its copy, and selected sources remained unchanged. These six outcomes are in private/controls/results.json.

No git/staging/commit, shared/old-root mutation, agents, heavy installs, browser UI, publication, uploads, submissions, contacts or downstream formal/manuscript/release work. The catalogue navigation violation and derivative/shared-ledger false admissions remain disclosed; artifact success does not erase them.

Reproduction: from the actual project root, run python frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153/tools/verify.py frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153 --final-sha <external FINAL hash> --manifest-sha <external MANIFEST hash> --report-sha <external REPORT hash>. The verifier does not write.
''')
print(json.dumps({'payload_files':len(files),'payload_bytes':sum(x['bytes'] for x in files),'outside_envelopes':3,'seal_completed':True}))
