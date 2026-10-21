from pathlib import Path
import hashlib,json,subprocess,os,stat
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r141');outside={'FINAL.md','MANIFEST.json','REPORT.md'}
assert not any((R/x).exists() for x in outside),'one-time seal already exists'
def h(b):return hashlib.sha256(b).hexdigest()
files={};dirs=[]
for d,ds,fs in os.walk(R,followlinks=False):
 for n in ds:
  p=Path(d)/n;assert stat.S_ISDIR(p.lstat().st_mode) and not p.is_symlink();dirs.append(str(p.relative_to(R)))
 for n in fs:
  p=Path(d)/n;assert stat.S_ISREG(p.lstat().st_mode);b=p.read_bytes();files[str(p.relative_to(R))]={'size':len(b),'sha256':h(b)}
# Original observations are checked separately, not inferred from reduced-copy membership.
o=json.loads((R/'original-authentication.json').read_text())
for x in o['files']:
 b=Path(x['canonical_original_path']).read_bytes();assert len(b)==x['size'] and h(b)==x['sha256'],x['canonical_original_path']
m={'schema':'r141-exact-payload-v1','outside_envelopes':sorted(outside),'directories':sorted(dirs),'files':dict(sorted(files.items()))}
(R/'MANIFEST.json').write_text(json.dumps(m,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
mh=h((R/'MANIFEST.json').read_bytes())
(R/'FINAL.md').write_text('''# Analytic discovery r141: PREFREEZE / no nominee

Codex / GPT-6 Astra / high / default service tier. Campaign19/20, latestR041. Parent alone integrates, reviews and counts. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs stipulated true.

No exact theorem was frozen and no full author-proof nominee is submitted. One family was pursued: Source376 forced-fluid computation. No correctness, contribution, acceptance or count is self-assigned.

The integrated derivation composes exact drift-conjugated solenoidal kicks, finite-volume reachable-set growth, the full Navier–Stokes residual, mean-zero compatibility and periodic Leray projection. It permits arbitrarily small time-dependent force errors in any prescribed finite smooth norm to steer the fixed particle into any nonempty open detector. This is credited supporting classical/source composition, not a substantial nominee or a restricted replacement for an old target.

The unpaid operation is the analogous prescribed-particle detector change with the perturbed force stationary from the fixed time one. The same ramp/residual formula works if an adequate stationary spatial perturbation exists, but the required derivative-controlled construction is absent. C1 connecting results do not supply small viscous residuals; the explicit shear test shows only that norm implication fails. The existing spatial clock repeats a table and does not automatically encode a different correction at each later step. No universal impossibility, worldwide-open, priority or exhaustion claim.

Read DERIVATION.md for the full calculation and GAPS.md for the precise stopping point. READING-LIMITS.md records the full ES proof read, selected companion and primary/transitive reads, failures, late reads and history omissions. ISOLATION.md records the initial faulty filename traversal and later derivative-role false admissions; no perfect isolation is claimed. No peer body or activity inference supplies a premise. Old C80/I85/I86 and all other full scopes/dispositions remain unchanged.

The protected inputs remain private/local under their original rights. No downstream formal/manuscript/release or external publishing action occurred.

Payload manifest SHA256: '''+mh+'\n')
(R/'REPORT.md').write_text('''# Outside payload report

Outcome: PREFREEZE / no nominee. See FINAL.md, DERIVATION.md and GAPS.md. This is discovery-only; no independent mathematical gates have been run.

Exact local payload: '''+str(len(files))+''' files and '''+str(len(dirs))+''' directories, plus the three outside envelopes FINAL.md, MANIFEST.json, REPORT.md. Source authentication binds 73 pinned selected blobs to the complete13223-entry canonical tree. Original authentication and selected-copy membership are separate. Thirteen named current originals were rechecked before this one-time seal and match the recorded late observations; this is not an earlier-history or OS snapshot certificate.

Six proportionate copied-fixture controls met their expected artifact outcomes: baseline/restored accepted; changed source bytes, missing payload, extra hidden payload and wrong external manifest anchor rejected. Every verifier invocation preserved the fixture snapshot. The fixture was independently inventoried; no old original manifest certifies a reduced copy. These are artifact checks, not proof or significance tests.

The final external handoff supplies independently computed SHA256 anchors for all three envelopes. verify.py requires those anchors, checks exact payload files/directories and pinned source Gitblob/size/SHA256 bindings, and only reads. The terminal replay and independent hash comparison occur after this report is written; this report does not substitute for their results.

Rights: original prose/code and named metadata are separate from protected source/primary/history/search/extracted/rendered/copied bodies in private/. No publication, upload, submission, contact or browser UI work.

Payload manifest SHA256: '''+mh+'\n')
anchors={x:h((R/x).read_bytes()) for x in sorted(outside)}
# GNU coreutils is a second implementation, independent of Python hashlib calls above.
p=subprocess.run(['sha256sum',*(str(R/x) for x in sorted(outside))],text=True,capture_output=True,check=True)
ind={Path(line.split('  ',1)[1]).name:line.split('  ',1)[0] for line in p.stdout.splitlines()}
assert anchors==ind
before={str(p.relative_to(R)):h(p.read_bytes()) for p in R.rglob('*') if p.is_file()}
cmd=['python','-B',str(R/'verify.py'),str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
v=subprocess.run(cmd,text=True,capture_output=True,check=True)
after={str(p.relative_to(R)):h(p.read_bytes()) for p in R.rglob('*') if p.is_file()};assert before==after
print(v.stdout.strip());print('Independent hashlib/coreutils hashes agree; final verifier did not change root files.')
for name,value in anchors.items():print(name,value)
