from pathlib import Path
import hashlib,json,subprocess,sys
base=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162m')
root=base/'packet/private/controls'
p=root/'packet';p.mkdir(parents=True,exist_ok=True)
paragraph=(base/'packet/AUTHOR-PROOF.md').read_text().split('\n\n')[1]+'\n'
(p/'own-text.txt').write_text(paragraph)
(p/'FINAL.md').write_text('Tiny copied own-text artifact control. This is not a mathematical review.\n')
(root/'REPORT.md').write_text('Fresh tiny control manifest; no inherited manifest and no protected source copies.\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():return {str(q.relative_to(root)):sha(q) for q in root.rglob('*') if q.is_file()}
manifest={'format':'r162m-exact-packet-v1','scope':'packet/','directories':['packet'],'files':[{'path':str(q.relative_to(root)),'bytes':q.stat().st_size,'sha256':sha(q)} for q in sorted(p.iterdir())]}
(root/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
anchors={k:sha(root/v) for k,v in [('final','packet/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]}
cmd=[sys.executable,str(base/'packet/verify_packet.py'),'--root',str(root),'--final-sha256',anchors['final'],'--manifest-sha256',anchors['manifest'],'--report-sha256',anchors['report']]
results=[]
def run(name,want):
 before=snapshot();r=subprocess.run(cmd,capture_output=True,text=True);after=snapshot()
 assert r.returncode==want,(name,r.stdout,r.stderr)
 assert before==after,'verifier wrote files'
 results.append({'case':name,'exit_code':r.returncode,'output':r.stdout.strip(),'read_only_snapshot_equal':True})
run('intact copied own text',0)
f=p/'own-text.txt';b=f.read_bytes();f.write_bytes(b+b'changed\n');run('copied payload byte change',1);f.write_bytes(b)
f.unlink();run('copied file missing',1);f.write_bytes(b)
x=p/'extra.txt';x.write_text('extra own text\n');run('extra copied file',1);x.unlink()
f=root/'REPORT.md';b=f.read_bytes();f.write_bytes(b+b'changed\n');run('outside REPORT anchor change',1);f.write_bytes(b)
f=root/'MANIFEST.json';b=f.read_bytes();f.write_bytes(b+b' ');run('manifest detached anchor change',1);f.write_bytes(b)
f=p/'FINAL.md';b=f.read_bytes();f.write_bytes(b+b'changed\n');run('FINAL detached anchor change',1);f.write_bytes(b)
(base/'packet/private/ARTIFACT-CONTROLS.json').write_text(json.dumps({'purpose':'tiny freshly manifested copied own-text controls; not mathematical gates','copied_from':'AUTHOR-PROOF.md first prose paragraph','anchors':anchors,'results':results,'restored_to_original_control_bytes':snapshot()},indent=2)+'\n')
print(json.dumps(results,indent=2))
