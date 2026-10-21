"""One-time envelope writer, callable only for this owned root and its control copy."""
from pathlib import Path
import hashlib,json,os
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def seal(root,final,report):
    assert root==ROOT or ROOT in root.parents
    assert not any((root/n).exists() for n in ('FINAL.md','MANIFEST.json','REPORT.md')),'already sealed'
    files={};dirs=[]
    for b,ds,fs in os.walk(root):
        dirs.append(Path(b).relative_to(root).as_posix())
        for n in fs:
            p=Path(b)/n;assert not p.is_symlink() and p.stat().st_nlink==1
            files[p.relative_to(root).as_posix()]={'bytes':p.stat().st_size,'sha256':sha(p)}
    (root/'MANIFEST.json').write_text(json.dumps({'schema':'r149-exact-tree-v1','directories':sorted(dirs),'files':dict(sorted(files.items()))},indent=2)+'\n')
    mh=sha(root/'MANIFEST.json');(root/'FINAL.md').write_text(final+'\nMANIFEST SHA256: '+mh+'\n')
    fh=sha(root/'FINAL.md');(root/'REPORT.md').write_text(report+'\nFINAL SHA256: '+fh+'\nMANIFEST SHA256: '+mh+'\n')
    return {'FINAL.md':fh,'MANIFEST.json':mh,'REPORT.md':sha(root/'REPORT.md')}
if __name__=='__main__':
    final='''# Structural discovery r149 — PREFREEZE / no nominee

Two families including the initial screen: Source174 thin trees; sustained Source169 circular chromatic elementary positivity. No full theorem was frozen or proved. No correctness/contribution/acceptance/count assigned; parent alone reviews and integrates.

The strongest integrated calculation is in notes/02-integrated-reduction-and-gap.md. Hikita scalar identities, Vailaya’s finite q=1 basis, and finite-state reachability/observability supply a rational graded trace reduction. The circular two-color argument also extends independent-set commutation and the exact Cauchy coefficient kernel. These compatible known operations are credited, not nominated.

Unpaid: a uniform coefficientwise N[q] positive evaluation of every elementary coefficient of the circular boundary trace (or equivalent graph alphabet), including all sizes, partitions and permitted antiparallel arcs. Positive real-q rational weights are insufficient; individual closed walks can retain denominators. Complete directed boundary endpoint/arc bookkeeping is not established at all conventions. No full-scope positive boundary cancellation was obtained.

366 exact trace comparisons and 368 closed-walk probes are bounded supporting diagnostics, not a theorem or a mathematical gate. Notes00–03 disclose provenance, prefreeze calculations, exact residual, late reads, truncations, source/primary/history extents, coarse false admissions/omissions and rights. All old full scopes and verdicts remain unchanged. No impossibility, exhaustion, perfect-isolation or priority claim.

All work is local to this exclusive root. No nested agents, git edits, publication, contacts, browser UI, formal/manuscript/release work or shared-root changes. Authorized Codex / GPT-6 Astra / high / default service tier; campaign19/20 latestR041. Pin and operative source proofs stipulated true.
'''
    report='''# Outside handoff report — r149

PREFREEZE / no nominee. Read FINAL.md and notes/02-integrated-reduction-and-gap.md for the result and exact unpaid operation; notes/03-evidence-and-reading-limits.md for evidence bounds. This envelope is outside the manifest payload but inside the exclusive owned root.

MANIFEST.json binds every payload file and directory exactly. FINAL.md binds that manifest; this REPORT binds both. Supply all three detached SHA256 anchors from the final handoff to code/verify.py. The verifier is read-only and performs no mathematical execution. private/control-results.json records proportionate copied controls with a separately generated reduced-copy manifest. private/incoming-authentication.json separately records canonical incoming-source authentication and late local original snapshots. No original manifest certifies the reduced copy. Integrity is not mathematical review.

No new acceptance or count is requested. Parent retains sole authority to integrate and review. No downstream work is included.
'''
    print(json.dumps(seal(ROOT,final,report),indent=2))
