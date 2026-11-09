from pathlib import Path
import datetime,hashlib,json,os,stat
r=Path(__file__).resolve().parent.parent
assert not (r/'FINAL.json').exists() and not (r/'packet/MANIFEST.json').exists(), 'One-time seal already exists'
def sha(b):return hashlib.sha256(b).hexdigest()
p=r/'packet';ff={};dd={'.':stat.S_IMODE(p.stat().st_mode)}
for base,ds,fs in os.walk(p,followlinks=False):
 for n in sorted(ds):
  q=Path(base)/n;st=q.lstat();assert stat.S_ISDIR(st.st_mode);dd[q.relative_to(p).as_posix()]=stat.S_IMODE(st.st_mode)
 for n in sorted(fs):
  q=Path(base)/n;st=q.lstat();assert stat.S_ISREG(st.st_mode) and st.st_nlink==1;b=q.read_bytes();ff[q.relative_to(p).as_posix()]=dict(bytes=len(b),sha256=sha(b),mode=stat.S_IMODE(st.st_mode))
m=dict(format='r138-exact-payload-v1',files=dict(sorted(ff.items())),directories=dict(sorted(dd.items())))
mp=p/'MANIFEST.json';mp.write_text(json.dumps(m,indent=2)+'\n');mh=sha(mp.read_bytes());rh=sha((r/'REPORT.md').read_bytes())
f=dict(format='r138-author-prefreeze-v1',status='PREFREEZE/no nominee',scope_frozen=False,
 runner='Codex / GPT-6 Astra',reasoning='high',serviceTier='default',source_pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
 mathematical_gates='none; parent alone integrates, reviews and counts',publication='STOPPED',
 sealed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exclusive_root=str(r),
 manifest_sha256=mh,report_sha256=rh,payload_files=len(ff),outside_unsealed=['work/','FINAL.sha256','MANIFEST.sha256','REPORT.sha256'])
fp=r/'FINAL.json';fp.write_text(json.dumps(f,indent=2)+'\n');fh=sha(fp.read_bytes())
for n,h in [('FINAL',fh),('MANIFEST',mh),('REPORT',rh)]: (r/(n+'.sha256')).write_text(h+'\n')
print(json.dumps(dict(final=fh,manifest=mh,report=rh,payload_files=len(ff)),indent=2))
