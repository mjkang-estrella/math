"""One own-root seal after proportionate disposable-copy controls. Never mutates originals."""
from pathlib import Path
import os,sys,hashlib,json,subprocess,importlib.util
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r155')
assert not (R/'MANIFEST.json').exists(),'already sealed'
spec=importlib.util.spec_from_file_location('verify_r155',R/'original/verify_readonly.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
F=R/'seal/copied-control';F.mkdir()
for source,target in [('original/verify_readonly.py','verify_readonly.py'),('notes/01-prefreeze-calculations.md','sample.md')]: (F/target).write_bytes((R/source).read_bytes())
for name in ['FINAL.md','REPORT.md']:(F/name).write_text('Disposable r155 integrity fixture only. No mathematical grade.\n')
(F/'MANIFEST.json').write_text(json.dumps(mod.inventory(F),indent=2)+'\n')
anchors={name:mod.digest((F/name).read_bytes()) for name in mod.ENVELOPES}
records=[]
def snapshot(root):
 d=[]
 for base,ds,fs in os.walk(root):
  for n in ds+fs:
   p=Path(base)/n;s=p.lstat();d.append((str(p.relative_to(root)),s.st_mode,s.st_nlink,mod.digest(p.read_bytes()) if p.is_file() else None))
 return sorted(d)
def test(label,expected,a=None):
 a=a or anchors;before=snapshot(F)
 p=subprocess.run([sys.executable,'-B',str(F/'verify_readonly.py'),str(F),'--final',a['FINAL.md'],'--manifest',a['MANIFEST.json'],'--report',a['REPORT.md']],capture_output=True,text=True,timeout=10)
 assert (p.returncode==0)==expected,(label,p.stdout,p.stderr)
 assert before==snapshot(F),'verifier mutated its input'
 records.append({'control':label,'expected_accept':expected,'exit':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip(),'copy_unchanged_by_verifier':True})
test('baseline',True)
p=F/'sample.md';original=p.read_bytes();p.write_bytes(original+b'changed');test('changed payload',False);p.write_bytes(original)
p.unlink();test('missing payload',False);p.write_bytes(original)
p=F/'.hidden-extra';p.write_text('extra');test('hidden extra',False);p.unlink()
p=F/'empty-extra';p.mkdir();test('extra empty directory',False);p.rmdir()
a=dict(anchors);a['MANIFEST.json']='0'*64;test('wrong detached manifest anchor',False,a)
p=F/'REPORT.md';original=p.read_bytes();p.write_bytes(original+b'changed');test('changed REPORT',False);p.write_bytes(original)
test('restored',True)
(R/'seal/control-results.json').write_text(json.dumps({'fixture_anchors':anchors,'results':records},indent=2)+'\n')
# Verify byte identity of specifically retained incoming originals without editing any.
orig=json.loads((R/'private/incoming-original-identities.json').read_text())
for x in orig:
 b=Path(x['original_path']).read_bytes();assert len(b)==x['size'] and mod.digest(b)==x['sha256'],x['original_path']
(R/'private/originals-final-recheck.json').write_text(json.dumps({'named_originals':len(orig),'all_match_incoming_identities':True,'semantic_coverage':'only extents recorded in note03'},indent=2)+'\n')
# These two envelopes were prepared before this command. Their own hashes are detached.
assert (R/'FINAL.md').is_file() and (R/'REPORT.md').is_file()
manifest=mod.inventory(R);(R/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'anchors':{name:mod.digest((R/name).read_bytes()) for name in mod.ENVELOPES},'payload_files':len(manifest['files']),'directories':len(manifest['directories']),'controls':len(records)},indent=2))
