#!/usr/bin/env python3
"""One production seal; refuses to overwrite any existing anchor file."""
from pathlib import Path
import datetime,hashlib,json,runpy,sys
sys.dont_write_bytecode=True
r=Path(__file__).resolve().parents[1]
for n in ['FINAL.json','MANIFEST.json','REPORT.md']:assert not (r/n).exists(),n+' already exists; refusing reseal'
ns=runpy.run_path(str(r/'verify.py'));h=ns['digest'];m=ns['inventory'](r)
assert h(r/'public/SCOPE.md')==ns['SCOPE']
report='''# Arithmetic/algebra r102 handoff

**FROZEN FULL-SCOPE AUTHOR-PROOF NOMINEE: T009P102.**
Independent correctness and substantial-contribution review are UNREVIEWED.
No acceptance, priority, count or downstream gate is assigned.

For every prime p, every finite n>=1, and function fields K/k,L/l of
transcendence degree at least two over algebraically closed fields of
characteristic p, every isomorphism of K_1^M/p^n preserving the degree-two
Steinberg relation submodule is a unique unit multiple of a unique actual
field isomorphism respecting the named bases. No integral or inverse-limit
lift is supplied. The known n=1 case is the stipulated pinned source.

The proposed core operation classifies all F_p-linear first-order
Steinberg-compatible endomorphisms as scalar, for every field of finite
p-rank at least two. The proof turns the mixed relation at f and f+1 into
two logarithmic derivatives along each transverse Euler coordinate;
Jacobson's classical identity eliminates those components. Multiplication
and p-basis intersections identify the remaining scalar. The subsequent
finite-level induction is routine and uses classical no-p-torsion of K_2.

Read public/SCOPE.md (immutable exact statement), public/PROOF.md
(280-line full proof), public/COMPARISON.md (strongest reductions and
contribution limits), and public/READINGS.md (actual reads and chronology).
The claim is not a new name for r101 DEG, r99 FS/FP, or r97/r98 noninjective
Hom transfers. r97's actual work note already proposed the higher-p-power
infinitesimal route; that antecedent and all classical/source operations
are credited. The core argument is short and may be judged technical by
an independent reviewer. No substantial verdict is asserted by its author.
No author mathematical gap remains identified at the unchanged frozen
scope; this is not independent correctness.

Freeze occurred at 2026-10-20T20:53:25.079473+00:00 after disclosed
prefreeze feasibility and before extended proof drafting. Late focused
history search, CP page-image checks, clarification of CP quotient
 definitions, and completion of a previously truncated mod-ell introductory
read are disclosed. No frozen bytes were changed. The actual source's
five equal-characteristic proof sections, the relevant companion proof
interfaces, Jacobson's logarithmic identity/proof, Geisser--Levine's
no-p-torsion theorem/proof, and Cadoret--Pirutka's stronger descent were
read. Authentication of all 27 acquired pinned files is not a claim to
have semantically read all 27 or all primary proof dependencies.

The complete 13223-entry nontruncated preprint tree and pinned raw bodies
are authenticated. Protected source/primary/history/search/render evidence
remains private under original rights; original research prose is separate.
All active exclusions, failed acquisitions, compressed raw-search evidence
and search-domain limitations are recorded. No worldwide-priority or
exhaustion claim is made.

Nine copied preseal integrity controls behaved as expected; the then-existing
owned tree and 14 named current originals were unchanged during controls.
At final observation, 13 of the 14 named originals still matched their
acquisition copies; the mutable NEW-TEN campaign ledger had changed outside
this task. It was not reread or adopted as a new mathematical input. Its
acquisition copy remains intact. This is not a whole-workspace preservation
claim. The read-only verifier requires externally supplied full FINAL,
MANIFEST and REPORT SHA256 anchors. Its checks are artifact checks only.

The manifest covers PAYLOAD_FILES payload files and PAYLOAD_DIRS directories,
including scratch. This REPORT is outside the manifest and separately
anchored; FINAL binds REPORT and MANIFEST and is itself anchored by the
terminal handoff. The production root is sealed once.

Runner: Codex / GPT-6 Astra / high / default service tier as authorized.
All writes stayed in fresh-arithmetic-discovery-r102. No git/staging/commit,
shared edits, nested agents, browser UI, contacts, uploads, submissions,
formalization, manuscript or release work occurred. Publication remains
stopped. Parent alone integrates and requests separate correctness,
contribution and any later gates. No count change is claimed.
'''.replace('PAYLOAD_FILES',str(len(m['files']))).replace('PAYLOAD_DIRS',str(len(m['directories']))).replace('\n definitions','\ndefinitions')
(r/'REPORT.md').write_text(report)
m['format']='r102-exact-payload-v1';m['outside']=['FINAL.json','MANIFEST.json','REPORT.md']
(r/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
f={'format':'r102-detached-final-v1','sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'FROZEN_FULL_SCOPE_AUTHOR_PROOF_NOMINEE','claim':'T009P102','mathematical_gates':'UNREVIEWED','independent_correctness':'UNREVIEWED','independent_contribution':'UNREVIEWED','author_gap_identified':None,'acceptance_claimed':False,'count_claimed':False,'publication':'STOPPED','scope_sha256':h(r/'public/SCOPE.md'),'proof_sha256':h(r/'public/PROOF.md'),'manifest_sha256':h(r/'MANIFEST.json'),'report_sha256':h(r/'REPORT.md'),'payload_files':len(m['files']),'payload_directories':len(m['directories']),'pinned_bodies':27,'copied_integrity_cases':9,'limits':'See public/READINGS.md and public/COMPARISON.md. Artifact seal is not mathematical review. Detached FINAL anchor must come from the handoff.'}
(r/'FINAL.json').write_text(json.dumps(f,sort_keys=True,indent=2)+'\n')
print(json.dumps({'FINAL':h(r/'FINAL.json'),'MANIFEST':h(r/'MANIFEST.json'),'REPORT':h(r/'REPORT.md'),'files':len(m['files']),'directories':len(m['directories'])},indent=2))
