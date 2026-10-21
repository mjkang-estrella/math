"""Bounded controls on a separately manifested small copy, inside own root only."""
from pathlib import Path
import hashlib,json,os,stat,subprocess,sys
ROOT=Path('frontier/campaigns/2026-10-14/structural-r161-contribution-r1')
COPY=ROOT/'private/copied-controls'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(p):
    s=p.stat();return {'sha256':sha(p),'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'links':s.st_nlink}
originals=[ROOT/'review.md',ROOT/'tools/verify.py'];before={str(p):snap(p) for p in originals}
COPY.mkdir(exist_ok=False)
(COPY/'derivation-copy.txt').write_bytes((ROOT/'review.md').read_bytes())
(COPY/'control.txt').write_text('Selected-copy integrity control; not mathematical evidence.\n')
(COPY/'FINAL.md').write_text('Selected-copy control only.\n')
(COPY/'REPORT.md').write_text('No original full manifest inherited.\n')
files={p.name:{'size':p.stat().st_size,'mode':stat.S_IMODE(p.stat().st_mode),'sha256':sha(p)} for p in COPY.iterdir() if p.name not in ('FINAL.md','REPORT.md')}
(COPY/'MANIFEST.json').write_text(json.dumps({'schema':'structural-r161-contribution-r1-exact-v1','directories':{},'files':dict(sorted(files.items()))},indent=2)+'\n')
anchors=[sha(COPY/name) for name in ('FINAL.md','MANIFEST.json','REPORT.md')]
rows=[]
def run(name,expected,aa=None):
    p=subprocess.run([sys.executable,'-B',str(ROOT/'tools/verify.py'),str(COPY),*(aa or anchors)],capture_output=True,text=True,timeout=15)
    ok=(p.returncode==0);rows.append({'control':name,'expected_match':expected,'observed_match':ok,'output':p.stdout.strip()});assert ok==expected
run('baseline selected copy',True)
p=COPY/'control.txt';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('changed selected bytes',False);p.write_bytes(b)
p.rename(COPY/'absent.txt');run('missing and unexpected member',False);(COPY/'absent.txt').rename(p)
extra=COPY/'extra.txt';extra.write_text('unexpected\n');run('extra member',False);extra.unlink()
mode=p.stat().st_mode&0o777;p.chmod(0o400);run('changed selected mode',False);p.chmod(mode)
run('wrong detached FINAL anchor',False,['0'*64,*anchors[1:]])
run('restored selected copy',True)
after={str(p):snap(p) for p in originals};assert before==after
(ROOT/'private/metadata/copied-control-results.json').write_text(json.dumps({'controls':rows,'source_target_before':before,'source_target_after':after,'unchanged':before==after,'atime_bound':False},indent=2)+'\n')
print('Seven expected control outcomes; original review/verifier bytes, modes, mtime and links unchanged.')
