"""One final seal writer, confined to this exclusive r111 root."""
from pathlib import Path
import hashlib,json,os
R=Path(__file__).resolve().parents[2];P=R/'packet'
assert set(x.name for x in R.iterdir())=={'packet','REPORT.md'}
assert not (P/'manifest.json').exists()
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files=[];dirs=[]
for d,ds,fs in os.walk(P,followlinks=False):
 for n in ds+fs:assert not (Path(d)/n).is_symlink()
 for n in ds:dirs.append((Path(d)/n).relative_to(P).as_posix())
 for n in fs:
  p=Path(d)/n;files.append({'path':p.relative_to(P).as_posix(),'size':p.stat().st_size,'sha256':h(p)})
files.sort(key=lambda x:x['path']);dirs.sort()
(P/'manifest.json').write_text(json.dumps({'schema':'r111-payload-v1','scope':'exact own research payload; no mathematical gate','directories':dirs,'files':files},indent=2)+'\n')
ph=h(P/'manifest.json');rh=h(R/'REPORT.md')
(R/'MANIFEST.json').write_text(json.dumps({'schema':'r111-outside-v1','packet_manifest_sha256':ph,'report_sha256':rh,'payload_count':len(files),'outside_files':['FINAL.json','MANIFEST.json','REPORT.md']},indent=2)+'\n')
mh=h(R/'MANIFEST.json')
(R/'FINAL.json').write_text(json.dumps({'schema':'r111-final-v1','status':'PREFREEZE/no nominee','statement_frozen':False,'mathematical_gates_assigned':False,'manifest_sha256':mh,'report_sha256':rh,'packet_manifest_sha256':ph,'payload_count':len(files),'provenance':'Codex / GPT-6 Astra / high / default service tier','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'},indent=2)+'\n')
print(json.dumps({'FINAL.json':h(R/'FINAL.json'),'MANIFEST.json':mh,'REPORT.md':rh,'packet/manifest.json':ph,'payload_count':len(files)},indent=2))
