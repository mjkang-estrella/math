"""Small reduced copies of OWN work, with their OWN manifests and anchors."""
import hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[1];C=R/'controls/fixture'
assert not C.exists();C.mkdir()
shutil.copy2(R/'notes/01-prefreeze-calculations.md',C/'copied-note.md')
shutil.copy2(R/'scripts/verify_packet.py',C/'verifier.py')
(C/'empty').mkdir()
(C/'FINAL.md').write_text('Reduced own-work control fixture, not an incoming original.\n')
(C/'REPORT.md').write_text('Membership is independently specified by this fixture manifest.\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap():
 out=[]
 for base,ds,fs in os.walk(C):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat()
   out.append((str(p.relative_to(C)),s.st_mode,sha(p) if p.is_file() else None))
 return sorted(out)
rows=[]
for name in ['copied-note.md','verifier.py']:
 p=C/name;rows.append(dict(path=name,size=p.stat().st_size,sha256=sha(p),mode=stat.S_IMODE(p.stat().st_mode)))
(C/'MANIFEST.json').write_text(json.dumps(dict(format='r147-exact-v1',files=rows,directories=['empty']),indent=2)+'\n')
anchors={x:sha(C/x) for x in ['FINAL.md','MANIFEST.json','REPORT.md']}
cmd=[sys.executable,'-B',str(R/'scripts/verify_packet.py'),str(C)]
for x,h in anchors.items():cmd+=['--'+x.split('.')[0].lower(),h]
results=[]
def run(name,ok,args=None):
 before=snap();q=subprocess.run(args or cmd,capture_output=True,text=True);after=snap()
 assert before==after,'verifier mutated fixture'
 assert (q.returncode==0)==ok,(name,q.stdout,q.stderr)
 results.append(dict(name=name,expected_accept=ok,returncode=q.returncode,unchanged=True))
run('baseline',True)
p=C/'copied-note.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('changed payload',False);p.write_bytes(b)
p.unlink();run('missing payload',False);p.write_bytes(b)
p=C/'.extra';p.write_text('extra');run('hidden extra',False);p.unlink()
p=C/'extra-empty';p.mkdir();run('extra empty directory',False);p.rmdir()
bad=cmd.copy();bad[-1]='0'*64;run('wrong detached report anchor',False,bad)
run('restored',True)
(R/'private/copied-controls.json').write_text(json.dumps({'kind':'Reduced copies of two OWN files; no original copied manifest used','anchors':anchors,'checks':results},indent=2)+'\n')
print(json.dumps(results))
