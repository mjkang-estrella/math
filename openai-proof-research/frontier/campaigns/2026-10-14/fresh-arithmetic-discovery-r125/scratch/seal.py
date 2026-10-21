"""One final seal; refuses to overwrite any main envelope."""
from pathlib import Path
import json,hashlib,os,stat
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125')
for name in ['FINAL.md','MANIFEST.json','REPORT.md']:assert not (R/name).exists(), 'already sealed'
# Remove only this run's unneeded bytecode and empty initial envelope directory.
p=R/'scratch/__pycache__'
if p.exists():
 for q in p.iterdir():
  assert q.is_file() and q.name.startswith('guard.') and q.suffix=='.pyc';q.unlink()
 p.rmdir()
p=R/'envelopes'
if p.exists():p.rmdir()
# Recheck exact acquired canonical identities and stable required originals.
for x in json.loads((R/'private/source-identities.json').read_text()):
 b=(R/x['copy']).read_bytes()
 assert len(b)==x['size'] and hashlib.sha256(b).hexdigest()==x['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']
incoming=json.loads((R/'private/incoming-identities.json').read_text());stable=0
for x in incoming['full_and_selected']:
 if x['kind'].startswith('whole original'):
  b=Path(x['original']).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'];stable+=1
files={};dirs=[]
for dp,ds,fs in os.walk(R,topdown=True,followlinks=False):
 for name in sorted(ds):
  p=Path(dp)/name;assert p.is_dir() and not p.is_symlink();dirs.append(p.relative_to(R).as_posix())
 for name in sorted(fs):
  p=Path(dp)/name;st=p.lstat();assert stat.S_ISREG(st.st_mode) and st.st_nlink==1
  b=p.read_bytes();files[p.relative_to(R).as_posix()]={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
final='''# Arithmetic discovery r125: PREFREEZE / no nominee

Authorized Codex / GPT-6 Astra / high / default service tier. Campaign19/20, latestR041 is incoming context; no count or independent grade is assigned. Parent alone integrates/reviews/counts. Publication and downstream stages remain stopped.

One distinct family was developed: finite-field polynomial arithmetic and roots in explicit finite commutative algebras. The integrated calculation is [notes/integrated-finite-algebra-reduction.md](notes/integrated-finite-algebra-reduction.md); prefreeze chronology is [notes/feasibility.md](notes/feasibility.md).

The strongest paid composition computes the nilradical and canonical coefficient algebra by Frobenius, splits all components using the stipulated prime-field factoring algorithm, and factors over arbitrary explicit extension fields. It gives exact simple-root lifting, the complete square-zero root problem, all pure Frobenius equations, and unit powers p^s m with runtime polynomial in D,log p,m,log(s+1). Dependence on m is numerical, not logarithmic. Existing regular-local algorithms also pay substantial singular lifting. These are source/classical compositions, not substantial nominees.

For nonunit square roots with radical cube zero, the note gives an exact arbitrary-quadratic-system encoding. A3CNF formula with n variables and c clauses produces a local F3-algebra of dimension3+2n+3c and a nonzero square-zero target, with root count2*3^(1+n+2c)*#SAT. This is a routine source-independent algebraization and a diagnostic of what a general solver would have to handle, not a nominated new hardness result. No dimension-uniform singular solver, new nonroutine special-class construction, or substantial source-dependent theorem closed. An uncomputed general solver is not submitted as a finding.

Ten bounded exact diagnostic records matched, including3132 basis-triple associativity identities and one full6561-element enumeration. They do not prove a universal theorem or establish contribution. No frozen theorem/author-proof nominee, independent correctness/contribution grade, acceptance, priority, family-exhaustion or perfect-isolation claim exists.

READING.md records partial source/primary/history coverage, late copies, false navigation admissions, truncations, Lenstra timeout, modern-primary503 failures and limited web-PDF reading. In particular an initial acceptance extractor wrongly displayed journal preamble lines1–19; an opaque history derivative and shared OUTCOME alias entered history scans. Those contents supply no premise, but the admissions cannot be undone. No active/future peer body supplies a mathematical premise. Every old frozen scope/disposition is unchanged.

The packet is private/local where original rights require. MANIFEST.json binds exact payload members; FINAL.md,MANIFEST.json,REPORT.md are its three outside-payload envelopes. Verify with python -B verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256 using all three independently detached terminal anchors. Artifact integrity is not a mathematical gate.
'''
report=f'''# r125 artifact and reading report

Mathematical disposition: PREFREEZE / no nominee. No independent gates or count. See FINAL.md, READING.md and the integrated note.

This one-time seal binds {len(files)} payload files and {len(dirs)} directories, plus exactly three top-level envelopes (total {len(files)+3} files). It excludes no other member. Fifteen selected canonical pinned TeX blobs were rechecked for exact size,Gitblob SHA1,SHA256. Seven required whole originals were rehashed unchanged. Twelve incoming objects separate seven whole copies from five exact excerpts. The complete13223-entry tree's supplied SHA256 was checked; truncated tree.json was ignored. No original manifest was inherited for reduced membership.

Three primary PDFs were acquired: Friedl–Ronyai1985 scan(25pages,23viewed including a blank), IKRS arXiv0811.3165v2(partial reading), and BLQ HALv1 dated17November2011(selected proof ranges,3pages viewed). There are26 authenticated local renders. Lenstra author-host download timed out; the2024 Chakrabarti–Dwivedi–Saxena PDF returned503 twice locally, with limited theorem/final-proof reading through web extraction only. The complete transitive literature was not read; no priority certificate follows.

Two bounded history scans had4965/4891 UTF8 admissions,6095/6168 pruned paths,40errors each,76/350hits. Maximum admitted size45072338bytes, no size cutoff. Known incorrect admissions and coarse omissions are preserved in READING.md. No active-peer premise, source truth audit, git command, nested agent, publication or downstream stage occurred.

Exact diagnostic completed10records under a35second alarm; all finite comparisons matched. Copied integrity controls(own two-member payload, own envelopes, copied verifier) behaved as expected for baseline, mutation, missing member, hidden extra, extra directory, wrong manifest anchor and restoration. Every verifier call preserved its copy and both selected originals remained unchanged. These are artifact controls only.

verify.py is offline and read-only and requires three explicit detached SHA256 anchors. It checks exact payload filenames/directories/lengths/hashes, all envelope anchors, regular-file/single-link status and absence of symlinks. It does not bind modes/access times, authenticate unseen original bodies, or prove mathematics. Final root replay and external sha256sum anchors are returned in the terminal handoff, outside this sealed payload. No main payload writes occur after sealing.
'''
with (R/'FINAL.md').open('x') as f:f.write(final)
with (R/'REPORT.md').open('x') as f:f.write(report)
manifest={'schema':'r125-exact-v1','outside_payload_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':dict(sorted(files.items())),'directories':sorted(dirs)}
with (R/'MANIFEST.json').open('x') as f:f.write(json.dumps(manifest,indent=2)+'\n')
print('SEALED ONCE',len(files),'payload files',len(dirs),'directories;',stable,'stable whole originals rechecked.')
