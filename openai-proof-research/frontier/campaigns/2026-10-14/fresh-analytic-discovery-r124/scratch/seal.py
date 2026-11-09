from pathlib import Path
import hashlib,json,stat
r=Path(__file__).absolute().parents[1];p=r/'packet'
def rec(q):
 s=q.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
 return dict(bytes=s.st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest(),mode=stat.S_IMODE(s.st_mode))
f={};d={'.':stat.S_IMODE(p.stat().st_mode)}
for q in sorted(p.rglob('*')):
 s=q.lstat();n=str(q.relative_to(p))
 if stat.S_ISDIR(s.st_mode):d[n]=stat.S_IMODE(s.st_mode)
 else:f[n]=rec(q)
(r/'MANIFEST.json').write_text(json.dumps({'files':f,'directories':d},indent=2,sort_keys=True)+'\n')
final={'status':'PREFREEZE_NO_NOMINEE','frozen_target':None,'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','manifest':rec(r/'MANIFEST.json'),'outside_report':rec(r/'REPORT.md'),'public_report':rec(p/'public/report.md')}
(r/'FINAL.json').write_text(json.dumps(final,indent=2,sort_keys=True)+'\n')
print(json.dumps({'final_sha256':rec(r/'FINAL.json')['sha256'],'manifest_sha256':final['manifest']['sha256'],'outside_report_sha256':final['outside_report']['sha256'],'public_report_sha256':final['public_report']['sha256'],'payloads':len(f),'directories':len(d)},indent=2))
