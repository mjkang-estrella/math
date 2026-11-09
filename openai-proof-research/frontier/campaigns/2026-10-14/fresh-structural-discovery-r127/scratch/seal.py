from pathlib import Path
import json,hashlib,os,stat
r=Path(__file__).resolve().parents[1];p=r/'packet';files={};dirs={'.':stat.S_IMODE(p.stat().st_mode)}
for base,ds,fs in os.walk(p):
 for n in ds:
  q=Path(base)/n;assert q.is_dir() and not q.is_symlink();dirs[q.relative_to(p).as_posix()]=stat.S_IMODE(q.stat().st_mode)
 for n in fs:
  q=Path(base)/n
  if q==p/'MANIFEST.json':continue
  s=q.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
  b=q.read_bytes();files[q.relative_to(p).as_posix()]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'mode':stat.S_IMODE(s.st_mode),'nlink':1}
m={'schema':'r127-exact-packet-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','files':dict(sorted(files.items())),'directories':dict(sorted(dirs.items()))}
b=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode();(p/'MANIFEST.json').write_bytes(b);(r/'FINAL.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
public_hash=hashlib.sha256((p/'public/report.md').read_bytes()).hexdigest()
report=f'''# Structural r127 handoff\n\nPREFREEZE: no frozen target, no nominee, no assigned mathematical/contribution gate or count.\n\nFull-scope smooth spectral-generator and Hilbert–Schmidt ellipsoid-prefix questions remain unclosed. Finite smooth whitening and a length-dependent ellipsoid bound are supporting calculations, not replacement nominees. The other screens found stronger existing reductions or old gaps.\n\nRead packet/public/report.md, spectral-feasibility.md, ellipsoid-feasibility.md, other-screens.md and reading-limits.md. Private evidence must remain private. No shared edits, nested agents, git mutations, uploads, browser UI, contacts or downstream formal/manuscript work occurred.\n\nDetached manifest SHA256: `{hashlib.sha256(b).hexdigest()}`.\nPublic report SHA256: `{public_hash}`.\n\nRun the read-only verifier from the repository root:\n\n```sh\npython frontier/campaigns/2026-10-14/fresh-structural-discovery-r127/packet/public/verify.py --packet frontier/campaigns/2026-10-14/fresh-structural-discovery-r127/packet --finalhash frontier/campaigns/2026-10-14/fresh-structural-discovery-r127/FINAL.sha256 --tree sources/preprints-tree.json\n```\n\nCopied controls and original-preservation evidence are outside the packet in controls.json. They concern artifact integrity, not mathematics. The verifier requires an explicit detached FINAL; it cannot silently trust a packet-provided replacement.\n'''
(r/'REPORT.md').write_text(report);(r/'REPORT.sha256').write_text(hashlib.sha256(report.encode()).hexdigest()+'\n')
print('manifest',hashlib.sha256(b).hexdigest(),'public_report',public_hash,'outside_report',hashlib.sha256(report.encode()).hexdigest(),'files',len(files),'dirs',len(dirs))
