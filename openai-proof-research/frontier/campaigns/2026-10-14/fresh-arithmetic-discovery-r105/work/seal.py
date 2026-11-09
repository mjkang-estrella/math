from pathlib import Path
import json,hashlib,stat,os,datetime
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r105');P=R/'packet'
assert not (P/'MANIFEST.json').exists() and not (P/'FINAL.json').exists(),'single seal only'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={};dirs={'.':stat.S_IMODE(P.stat().st_mode)}
for base,ds,fs in os.walk(P,followlinks=False):
 for n in ds:
  p=Path(base)/n;assert p.is_dir() and not p.is_symlink();dirs[p.relative_to(P).as_posix()]=stat.S_IMODE(p.stat().st_mode)
 for n in fs:
  p=Path(base)/n;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
  files[p.relative_to(P).as_posix()]=dict(size=s.st_size,mode=stat.S_IMODE(s.st_mode),sha256=digest(p))
manifest=dict(schema=1,meaning='exact artifact payload inventory; no mathematical gate',files=dict(sorted(files.items())),directories=dict(sorted(dirs.items())))
(P/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');(P/'MANIFEST.json').chmod(0o644);(R/'REPORT.md').chmod(0o644)
final=dict(schema=1,status='PREFREEZE/no nominee',runner='Codex / GPT-6 Astra / high / default service tier',pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',stipulation='upstream statements and operative proof operations accepted true; no truth audit',sealed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=digest(P/'MANIFEST.json'),outside_report_sha256=digest(R/'REPORT.md'),supporting_scope_sha256=digest(P/'public/SUPPORT-SCOPE.md'),nominee=None,mathematical_gates='none assigned',rights='protected bodies local under original rights; no publication')
(P/'FINAL.json').write_text(json.dumps(final,indent=2,sort_keys=True)+'\n');(P/'FINAL.json').chmod(0o644)
anchors=dict(FINAL=digest(P/'FINAL.json'),MANIFEST=digest(P/'MANIFEST.json'),REPORT=digest(R/'REPORT.md'))
(R/'ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n');print(json.dumps(anchors,indent=2));print('payloads',len(files),'directories',len(dirs))
