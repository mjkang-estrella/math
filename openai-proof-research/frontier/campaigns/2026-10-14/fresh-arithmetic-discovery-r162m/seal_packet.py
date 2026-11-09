from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess,sys
root=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162m')
packet=root/'packet'
assert not (root/'MANIFEST.json').exists(),'Refuse to reseal'
assert not (root/'ANCHORS.json').exists(),'Refuse to replace detached anchors'
shutil.copyfile(root/'seal_packet.py',packet/'private/methods/seal_packet.py')
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
files=[];dirs=[]
for directory,names,leaves in os.walk(packet,followlinks=False):
 p=Path(directory);dirs.append(p.relative_to(root).as_posix())
 for name in names:
  assert not (p/name).is_symlink()
 for name in leaves:
  q=p/name;assert q.is_file() and not q.is_symlink()
  files.append({'path':q.relative_to(root).as_posix(),'bytes':q.stat().st_size,'sha256':sha(q)})
manifest={'format':'r162m-exact-packet-v1','scope':'packet/','seal_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'directories':sorted(dirs),'files':sorted(files,key=lambda v:v['path'])}
with (root/'MANIFEST.json').open('x') as f:f.write(json.dumps(manifest,indent=2)+'\n')
anchors={'FINAL':{'path':'packet/FINAL.md','sha256':sha(packet/'FINAL.md')},'MANIFEST':{'path':'MANIFEST.json','sha256':sha(root/'MANIFEST.json')},'REPORT':{'path':'REPORT.md','sha256':sha(root/'REPORT.md')}}
cmd=[sys.executable,str(packet/'verify_packet.py'),'--root',str(root),'--final-sha256',anchors['FINAL']['sha256'],'--manifest-sha256',anchors['MANIFEST']['sha256'],'--report-sha256',anchors['REPORT']['sha256']]
result=subprocess.run(cmd,capture_output=True,text=True)
assert result.returncode==0,(result.stdout,result.stderr)
with (root/'VERIFICATION.txt').open('x') as f:f.write(result.stdout)
with (root/'ANCHORS.json').open('x') as f:f.write(json.dumps({'format':'r162m-detached-anchors-v1','anchors':anchors,'artifact_verification':result.stdout.strip(),'meaning':'exact byte integrity only; no mathematical gate'},indent=2)+'\n')
print(result.stdout.strip());print(json.dumps(anchors,indent=2));print('Packet files:',len(files),'total bytes:',sum(v['bytes'] for v in files))
