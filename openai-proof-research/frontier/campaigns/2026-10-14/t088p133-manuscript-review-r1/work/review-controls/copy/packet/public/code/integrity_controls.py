#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Proportionate copied artifact controls; never mutate input packet.
Output directory must be inside the supplied draft root and outside packet/.
The fixture has a separately generated seal, not a mathematical verdict.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,stat,subprocess,sys
sys.dont_write_bytecode=True

def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
 out={}
 for p in [root]+sorted(root.rglob('*')):
  st=p.lstat();v={'mode':stat.S_IMODE(st.st_mode),'nlink':st.st_nlink}
  if p.is_symlink():v.update(kind='symlink',target=str(p.readlink()))
  elif p.is_dir():v.update(kind='directory')
  else:v.update(kind='file',bytes=st.st_size,sha256=h(p))
  out[str(p.relative_to(root))]=v
 return out

def fixture_seal(r):
 files={};dirs={'packet':{'mode':stat.S_IMODE((r/'packet').stat().st_mode)}}
 for p in sorted((r/'packet').rglob('*')):
  rel=p.relative_to(r).as_posix();st=p.stat()
  if p.is_dir():dirs[rel]={'mode':stat.S_IMODE(st.st_mode)}
  elif rel!='packet/MANIFEST.json':files[rel]={'bytes':st.st_size,'mode':stat.S_IMODE(st.st_mode),'sha256':h(p)}
 m=r/'packet/MANIFEST.json'
 if m.exists():m.chmod(0o644)
 m.write_text(json.dumps({'schema':'T088P133-manuscript-review-r1-exact-v1','files':files,'directories':dirs},indent=2)+'\n')
 (r/'REPORT.md').write_text('Copied artifact-control fixture only. No mathematical gate.\n')
 (r/'FINAL.json').write_text(json.dumps({'manifest_sha256':h(m),'report_sha256':h(r/'REPORT.md')},indent=2)+'\n')
 return {'final':h(r/'FINAL.json'),'manifest':h(m),'report':h(r/'REPORT.md')}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('root',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args();r=a.root.resolve();o=a.output.resolve()
 assert o.is_relative_to(r) and not o.is_relative_to(r/'packet') and o!=r
 assert not o.exists(),'use a fresh output directory'
 before=snapshot(r/'packet');o.mkdir(parents=True);fixture=o/'copy'
 cases=['intact','wrong_external_anchor','payload_byte','missing_payload','extra_payload','empty_directory','symlink_payload','hardlinked_payload','payload_mode','manifest_byte','final_byte','report_byte']
 results=[]
 for name in cases:
  if fixture.exists():shutil.rmtree(fixture)
  fixture.mkdir();shutil.copytree(r/'packet',fixture/'packet',symlinks=True)
  anchors=fixture_seal(fixture);target=fixture/'packet/public/README.md';args=dict(anchors)
  if name=='wrong_external_anchor':args['final']='0'*64
  elif name=='payload_byte':
   mode=target.stat().st_mode;target.chmod(0o644);data=target.read_bytes();target.write_bytes(bytes([data[0]^1])+data[1:]);target.chmod(stat.S_IMODE(mode))
  elif name=='missing_payload':target.unlink()
  elif name=='extra_payload':(fixture/'packet/public/extra.txt').write_text('extra')
  elif name=='empty_directory':(fixture/'packet/public/extra-dir').mkdir()
  elif name=='symlink_payload':
   extra=fixture/'symlink-target';shutil.copyfile(target,extra);target.unlink();target.symlink_to(extra)
  elif name=='hardlinked_payload':os.link(target,fixture/'hardlink-target')
  elif name=='payload_mode':target.chmod(stat.S_IMODE(target.stat().st_mode)^stat.S_IXUSR)
  elif name in ('manifest_byte','final_byte','report_byte'):
   f=fixture/({'manifest_byte':'packet/MANIFEST.json','final_byte':'FINAL.json','report_byte':'REPORT.md'}[name]);f.chmod(0o644);f.write_bytes(f.read_bytes()+b' ')
  b=snapshot(fixture)
  cmd=[sys.executable,'-B',str(r/'packet/public/verify.py'),str(fixture)]
  for k,v in args.items():cmd.extend(['--'+k+'-sha256',v])
  cp=subprocess.run(cmd,capture_output=True,text=True)
  after=snapshot(fixture);expected=0 if name=='intact' else 1
  row={'case':name,'expected_exit':expected,'actual_exit':cp.returncode,'read_only_snapshot_equal':b==after,'stdout':cp.stdout.strip(),'stderr':cp.stderr.strip(),'fixture_anchors':anchors}
  assert cp.returncode==expected and b==after,row
  results.append(row)
 assert snapshot(r/'packet')==before,'actual payload changed'
 out={'verifier_sha256':h(r/'packet/public/verify.py'),'scope':'12 separately sealed full-payload copied fixtures; same verifier; not mathematics or final acceptance','results':results,'actual_packet_unchanged':True}
 (o/'results.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'cases':len(results),'expected_outcomes':True,'read_only_all':True,'actual_packet_unchanged':True,'verifier_sha256':out['verifier_sha256']}))
if __name__=='__main__':main()
