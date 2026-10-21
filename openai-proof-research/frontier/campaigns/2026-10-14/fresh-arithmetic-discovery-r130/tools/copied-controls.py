"""Small disposable fixtures only; does not seal or mutate the actual packet."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r130');C=R/'controls'
ENV=['envelopes/FINAL.md','envelopes/MANIFEST.json','envelopes/REPORT.md']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
 out={}
 for b,ds,fs in os.walk(root):
  for f in fs:
   p=Path(b)/f;out[str(p.relative_to(root))]=sha(p)
 return out
B=C/'baseline';(B/'envelopes').mkdir(parents=True,exist_ok=False);(B/'notes').mkdir();(B/'tools').mkdir()
shutil.copyfile(R/'notes/reduction-boundary.md',B/'notes/reduction-boundary.md');shutil.copyfile(R/'tools/verify.py',B/'tools/verify.py')
(B/ENV[0]).write_text('Copied fixture only; no mathematical claim.\n');(B/ENV[2]).write_text('Fixture report only.\n')
files={};dirs=[]
for b,ds,fs in os.walk(B):
 for d in ds:dirs.append(str((Path(b)/d).relative_to(B)))
 for f in fs:
  p=Path(b)/f;s=str(p.relative_to(B))
  if s not in ENV:files[s]={'bytes':p.stat().st_size,'sha256':sha(p)}
(B/ENV[1]).write_text(json.dumps({'schema':'r130-exact-v1','excluded_envelopes':ENV,'files':files,'directories':sorted(dirs)},indent=2)+'\n')
anchors=[sha(B/e) for e in ENV];before=snapshot(B)
def run(root,expected,anchors=anchors):
 q=subprocess.run([sys.executable,str(root/'tools/verify.py'),str(root),'--final-sha',anchors[0],'--manifest-sha',anchors[1],'--report-sha',anchors[2]],capture_output=True,text=True)
 assert (q.returncode==0)==expected,(str(root),q.stdout,q.stderr)
 return {'fixture':str(root.relative_to(C)),'expected_valid':expected,'returncode':q.returncode,'output':(q.stdout+q.stderr).strip()}
results=[run(B,True),run(B,True)]
for name in ['alter-byte','extra-file','missing-file','wrong-anchor']:
 T=C/name;shutil.copytree(B,T)
 if name=='alter-byte':
  p=T/'notes/reduction-boundary.md';p.write_bytes(p.read_bytes()+b'changed\n')
 elif name=='extra-file':(T/'unlisted.txt').write_text('extra\n')
 elif name=='missing-file':(T/'notes/reduction-boundary.md').unlink()
 results.append(run(T,False,['0'*64,anchors[1],anchors[2]] if name=='wrong-anchor' else anchors))
assert snapshot(B)==before
(C/'results.json').write_text(json.dumps({'controls':results,'baseline_bytes_unchanged':True,'scope':'copied fixtures only, exact bytes/membership, no mathematical verdict'},indent=2)+'\n')
print(json.dumps({'positive':2,'negative':4,'baseline_bytes_unchanged':True}))
