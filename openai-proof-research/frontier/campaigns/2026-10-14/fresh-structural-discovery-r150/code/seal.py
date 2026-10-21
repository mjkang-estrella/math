"""One-time own sealing only; envelopes must not exist. Run from actual project root."""
from pathlib import Path
import os,json,hashlib,stat
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-structural-discovery-r150')
ENV={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def seal(root,final,report):
 assert not any((root/x).exists() for x in ENV),'already sealed/envelopes exist'
 payload={};dirs={''}
 for base,children,names in os.walk(root,followlinks=False):
  for name in children:
   p=Path(base)/name;assert stat.S_ISDIR(p.lstat().st_mode);dirs.add(p.relative_to(root).as_posix())
  for name in names:
   p=Path(base)/name;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
   b=p.read_bytes();payload[p.relative_to(root).as_posix()]={'size':len(b),'sha256':sha(b)}
 manifest={'schema':'r150-exact-payload-v1','envelopes':sorted(ENV),'directories':sorted(dirs),'payload':dict(sorted(payload.items()))}
 (root/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
 (root/'FINAL.md').write_text(final)
 (root/'REPORT.md').write_text(report)
 return {name:sha((root/name).read_bytes()) for name in sorted(ENV)}
if __name__=='__main__':
 print(json.dumps(seal(R,(R/'notes/final-envelope.txt').read_text(),(R/'notes/report-envelope.txt').read_text()),indent=2))
