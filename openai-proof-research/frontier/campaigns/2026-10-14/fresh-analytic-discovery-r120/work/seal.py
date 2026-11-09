from pathlib import Path
import hashlib,json,stat
r=Path(__file__).resolve().parents[1];p=r/'packet'
def sha(b):return hashlib.sha256(b).hexdigest()
e={}
for q in sorted(p.rglob('*')):
 s=q.lstat();rel=str(q.relative_to(p))
 if q.is_symlink():raise RuntimeError('symlink')
 if q.is_dir():e[rel]=dict(type='directory',mode=stat.S_IMODE(s.st_mode))
 else:
  assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
  b=q.read_bytes();e[rel]=dict(type='file',mode=stat.S_IMODE(s.st_mode),bytes=len(b),sha256=sha(b))
m=dict(schema='r120-manifest-v1',scope='packet',packet_mode=stat.S_IMODE(p.stat().st_mode),entries=e)
mb=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode();(r/'MANIFEST.json').write_bytes(mb)
f=dict(schema='r120-final-v1',status='PREFREEZE',frozen_target=None,pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',tree_sha256='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b',manifest_sha256=sha(mb),report_sha256=sha((p/'public/report.md').read_bytes()))
fb=(json.dumps(f,indent=2,sort_keys=True)+'\n').encode();(r/'FINAL.json').write_bytes(fb)
anchors=dict(final_sha256=sha(fb),manifest_sha256=sha(mb),report_sha256=f['report_sha256'])
(r/'ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n')
(r/'HANDOFF.md').write_text('''# Analytic discovery r120 handoff

PREFREEZE. No frozen target; no nominee; no count, gate or substantiality self-assignment. Six operative screens at unequal depth:078,219,366,341,083,090. Parent integration only.

Read packet/public/report.md and the three research notes. Smooth-phase Taylor/amplitude compatibility and normalized crack-tip tail calculation did not leave an identified unpaid operation. Atomic disorder retains microscopic averaging/conditional-centering and environment-matching gaps. Other screens and late antecedents are explicitly bounded. No claim of exhaustion or worldwide priority.

The packet includes19 canonical source bodies,5 primary PDF/text pairs and26 historical copies with actual reading limits. All raw sources are authenticated against the complete13,223-entry tree at the stipulated pin. Four unread acquisitions were removed, retaining metadata. Private bodies retain original rights. No external publication, shared edits or downstream formal/manuscript work.

Detached anchors (outside packet):

- FINAL SHA256: `'''+anchors['final_sha256']+'`\n- MANIFEST SHA256: `'+anchors['manifest_sha256']+'`\n- public/report.md SHA256: `'+anchors['report_sha256']+'`\n\nUse packet/public/verify.py with both independently supplied detached anchors. Copied final control results are in controls/receipt.json after execution; those controls are integrity checks, never mathematics.\n')
print(json.dumps(anchors))
