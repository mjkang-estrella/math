from pathlib import Path
import datetime,hashlib,json,stat
R=Path(__file__).resolve().parents[1]; packet=R/'packet'
assert not (packet/'FINAL.json').exists() and not (packet/'MANIFEST.json').exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={};dirs={}
for p in sorted(packet.rglob('*')):
 assert not p.is_symlink()
 mode=stat.S_IMODE(p.stat().st_mode)
 if p.is_dir():dirs[p.relative_to(packet).as_posix()]=mode
 else:
  assert p.is_file() and p.stat().st_nlink==1
  files[p.relative_to(packet).as_posix()]={'sha256':sha(p),'size':p.stat().st_size,'mode':mode}
manifest={'format':'r104-exact-payload-v1','seal_mode':420,'report_mode':stat.S_IMODE((R/'REPORT.md').stat().st_mode),'payloads':files,'directories':dirs}
(packet/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
final={'format':'r104-final-v1','sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PREFREEZE','nominee':None,'frozen_candidate':None,'runner':'Codex / GPT-6 Astra / high / default service tier','pinned_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','campaign_count_context':'19/20; no increment assigned','manifest_sha256':sha(packet/'MANIFEST.json'),'outside_report_sha256':sha(R/'REPORT.md'),'payload_count':len(files),'directory_count':len(dirs),'result':'Local stabilized tensor-growth derivations retained; full global upper inequality unproved','mathematical_gates':'Not self-awarded; parent independent stages unchanged','publication':'Stopped'}
(packet/'FINAL.json').write_text(json.dumps(final,indent=2,ensure_ascii=False)+'\n')
anchors={'packet/FINAL.json':sha(packet/'FINAL.json'),'packet/MANIFEST.json':sha(packet/'MANIFEST.json'),'REPORT.md':sha(R/'REPORT.md')}
(R/'ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n')
print(json.dumps({'anchors':anchors,'payloads':len(files),'directories':len(dirs)},indent=2))
