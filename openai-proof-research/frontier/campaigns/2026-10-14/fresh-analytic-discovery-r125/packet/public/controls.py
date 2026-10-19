#!/usr/bin/env python3
"""Copied integrity controls; explicit detached anchors required. No math tests. MIT."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(r):return {p.relative_to(r).as_posix():sha(p) for p in sorted(r.rglob('*')) if p.is_file()}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--final-sha256',required=True);ap.add_argument('--report-sha256',required=True);a=ap.parse_args();r=a.root.resolve()
 before=snapshot(r/'packet')|{'FINAL.json':sha(r/'FINAL.json'),'REPORT.md':sha(r/'REPORT.md')}
 results=[]
 names=['baseline','missing-final','wrong-final','wrong-report','payload-edit','payload-delete','extra-file','extra-directory','payload-symlink','directory-symlink','report-edit','final-edit','manifest-edit','reanchored-payload','canonical-edit','tree-truncated','primary-edit','read-only-audit']
 with tempfile.TemporaryDirectory(prefix='controls-',dir=r/'work') as td:
  for name in names:
   c=Path(td)/name;c.mkdir();shutil.copytree(r/'packet',c/'packet');shutil.copyfile(r/'FINAL.json',c/'FINAL.json');shutil.copyfile(r/'REPORT.md',c/'REPORT.md')
   v=c/'packet/public/verify.py';payload=c/'packet/public/renewal-feasibility.md'
   fh=a.final_sha256;rh=a.report_sha256
   if name=='wrong-final':fh='0'*64
   if name=='wrong-report':rh='0'*64
   if name=='payload-edit':payload.write_bytes(payload.read_bytes()+b'!')
   if name=='payload-delete':payload.unlink()
   if name=='extra-file':(c/'packet/EXTRA').write_text('extra')
   if name=='extra-directory':(c/'packet/EXTRA').mkdir()
   if name=='payload-symlink':payload.unlink();payload.symlink_to(c/'REPORT.md')
   if name=='directory-symlink':(c/'packet/EXTRA').symlink_to(c/'packet/public',target_is_directory=True)
   if name=='report-edit':(c/'REPORT.md').write_text('changed')
   if name=='final-edit':(c/'FINAL.json').write_text('{}')
   if name=='manifest-edit':(c/'packet/MANIFEST.json').write_text('{}')
   if name=='reanchored-payload':
    payload.write_bytes(payload.read_bytes()+b'!');mp=c/'packet/MANIFEST.json';m=json.loads(mp.read_text())
    for e in m['files']:
     if e['path']=='public/renewal-feasibility.md':e.update(bytes=payload.stat().st_size,sha256=sha(payload))
    mp.write_text(json.dumps(m));fp=c/'FINAL.json';f=json.loads(fp.read_text());f['manifest_sha256']=sha(mp);fp.write_text(json.dumps(f))
   if name=='canonical-edit':
    p=c/'packet/private/upstream/canonical-register.json';z=json.loads(p.read_text());z[0]['canonical']['sha']='0'*40;p.write_text(json.dumps(z))
   if name=='tree-truncated':
    p=c/'packet/private/context/preprints-tree.json';z=json.loads(p.read_text());z['truncated']=True;p.write_text(json.dumps(z))
   if name=='primary-edit':
    p=c/'packet/private/primary/zhan.txt';p.write_bytes(p.read_bytes()+b'!')
   args=['--root',str(c),'--final-sha256',fh,'--report-sha256',rh]
   if name=='missing-final':args=['--root',str(c),'--report-sha256',rh]
   cmd=[sys.executable,'-B',str(v),*args]
   if name=='read-only-audit':
    code="""import sys,runpy,os
p=sys.argv[1];sys.argv=sys.argv[1:]
def audit(event,args):
 if event=='open':
  mode=args[1];flags=args[2]
  if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):raise RuntimeError('write denied')
 if event in {'os.remove','os.rename','os.mkdir','os.rmdir','os.symlink','os.link','os.chmod','os.chown','os.truncate','subprocess.Popen'}:raise RuntimeError('mutation denied')
sys.addaudithook(audit);runpy.run_path(p,run_name='__main__')
"""
    cmd=[sys.executable,'-B','-c',code,str(v),*args]
   p=subprocess.run(cmd,capture_output=True,text=True);want=name in {'baseline','read-only-audit'}
   ok=(p.returncode==0)==want
   results.append({'case':name,'expected':'accept' if want else 'reject','exit':p.returncode,'matched':ok,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()})
   shutil.rmtree(c)
 after=snapshot(r/'packet')|{'FINAL.json':sha(r/'FINAL.json'),'REPORT.md':sha(r/'REPORT.md')}
 out={'kind':'INTEGRITY_CONTROLS_ONLY','detached_final':a.final_sha256,'detached_report':a.report_sha256,'cases':results,'original_sealed_files_unchanged':before==after,'all_expected':all(x['matched'] for x in results) and before==after}
 print(json.dumps(out,indent=2));return 0 if out['all_expected'] else 1
if __name__=='__main__':sys.exit(main())
