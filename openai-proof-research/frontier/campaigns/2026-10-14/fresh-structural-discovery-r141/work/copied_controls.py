from research import *
import importlib.util,shutil,subprocess,stat
spec=importlib.util.spec_from_file_location('verifier',OUT/'packet/public/verify_packet.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
fixture=OUT/'copied-controls/fixture';(fixture/'packet/public').mkdir(parents=True);(fixture/'empty-directory').mkdir()
for name in ['prefreeze-derivation.md','verify_packet.py']:shutil.copyfile(OUT/'packet/public'/name,fixture/'packet/public'/name)
m={'format':'r141-exact-root-v1','created_utc':now(),'root_mode':stat.S_IMODE(fixture.stat().st_mode),'entries':v.inventory(fixture)}
(fixture/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
mh=sha((fixture/'MANIFEST.json').read_bytes());(fixture/'outsideREPORT.md').write_text('Copied miniature artifact fixture only. No mathematical gate.\nManifest SHA256: '+mh+'\n')
rh=sha((fixture/'outsideREPORT.md').read_bytes());(fixture/'FINAL.json').write_text(json.dumps({'manifest_sha256':mh,'outside_report_sha256':rh,'purpose':'copied fixture'},indent=2)+'\n')
a={'MANIFEST.json':mh,'outsideREPORT.md':rh,'FINAL.json':sha((fixture/'FINAL.json').read_bytes())};(fixture/'ANCHORS.json').write_text(json.dumps(a,indent=2)+'\n')
base={p.relative_to(fixture).as_posix():p.read_bytes() for p in fixture.rglob('*') if p.is_file()}
def check(label,expected,anchors=None):
 aa=anchors or a
 cmd=['python','-B',str(fixture/'packet/public/verify_packet.py'),'--root',str(fixture),'--manifest-sha256',aa['MANIFEST.json'],'--report-sha256',aa['outsideREPORT.md'],'--final-sha256',aa['FINAL.json']]
 before={p.relative_to(fixture).as_posix():sha(p.read_bytes()) for p in fixture.rglob('*') if p.is_file() and not p.is_symlink()}
 r=subprocess.run(cmd,capture_output=True,text=True,timeout=20)
 after={p.relative_to(fixture).as_posix():sha(p.read_bytes()) for p in fixture.rglob('*') if p.is_file() and not p.is_symlink()}
 assert before==after,'verifier wrote fixture'
 assert r.returncode==expected,(label,r.stdout,r.stderr)
 results.append(dict(label=label,utc=now(),exit=r.returncode,result=json.loads(r.stdout),fixture_bytes_unchanged_during_verifier=True))
results=[];check('baseline',0)
p=fixture/'packet/public/prefreeze-derivation.md';original=p.read_bytes();p.write_bytes(original+b'changed\n');check('changed copied payload',1);p.write_bytes(original)
p=fixture/'extra.txt';p.write_text('extra');check('added copied file',1);p.unlink()
p=fixture/'empty-directory';p.rmdir();check('deleted copied empty directory',1);p.mkdir()
p=fixture/'packet/public/prefreeze-derivation.md';original=p.read_bytes();p.unlink();check('deleted copied payload',1);p.write_bytes(original)
check('wrong detached manifest SHA256',1,dict(a,**{'MANIFEST.json':'0'*64}))
p=fixture/'link';p.symlink_to('packet/public/prefreeze-derivation.md');check('copied fixture symlink',1);p.unlink()
p=fixture/'hardcopy';os.link(fixture/'packet/public/prefreeze-derivation.md',p);check('copied fixture hardlink',1);p.unlink()
for name in ['FINAL.json','outsideREPORT.md']:
 p=fixture/name;original=p.read_bytes();p.write_bytes(original+b'changed\n');check('changed copied '+name,1);p.write_bytes(original)
check('restored fixture',0)
assert base=={p.relative_to(fixture).as_posix():p.read_bytes() for p in fixture.rglob('*') if p.is_file()}
save('copied-controls.json',dict(recorded_utc=now(),scope='one miniature copied fixture; nine rejection cases, baseline and restored acceptance; byte/inventory tests only',anchors=a,cases=results,restored_all_copied_bytes=True,original_payload_not_mutated=True))
print(len(results),'copied integrity checks completed')
