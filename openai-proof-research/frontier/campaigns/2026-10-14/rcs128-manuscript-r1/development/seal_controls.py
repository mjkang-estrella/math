#!/usr/bin/env python3
"""Disposable-copy controls, outside frozen packet. MIT."""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,tempfile
p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=pathlib.Path);p.add_argument('--anchor',required=True);a=p.parse_args();root=a.root.resolve()
results=[]
def run(path,anchor):
 r=subprocess.run(['python3',str(root/'verify.py'),'--root',str(path),'--anchor',anchor],capture_output=True,text=True)
 return r.returncode,r.stdout+r.stderr
before={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}
with tempfile.TemporaryDirectory(prefix='rcs128-seal-controls-') as d:
 d=pathlib.Path(d)
 cases=['positive','wrong_anchor','malformed_anchor','changed','missing','extra','extra_empty_directory','missing_directory','symlink_file','symlink_root','symlink_ancestor','hardlink','fifo','recomputed_manifest_old_anchor']
 for i,c in enumerate(cases):
  t=d/str(i);shutil.copytree(root,t);rr=t;anchor=a.anchor;f=t/'public/article.tex'
  if c=='wrong_anchor':anchor='0'*64
  elif c=='malformed_anchor':anchor='wrong'
  elif c=='changed':f.write_bytes(f.read_bytes()+b'\n% mutation\n')
  elif c=='missing':f.unlink()
  elif c=='extra':(t/'extra.txt').write_text('extra')
  elif c=='extra_empty_directory':(t/'extra-empty').mkdir()
  elif c=='missing_directory':shutil.rmtree(t/'validation/pages')
  elif c=='symlink_file':f.unlink();f.symlink_to(root/'public/article.tex')
  elif c=='symlink_root':rr=d/'root-link';rr.symlink_to(t,target_is_directory=True)
  elif c=='symlink_ancestor':link=d/'parent-link';link.symlink_to(d,target_is_directory=True);rr=link/str(i)
  elif c=='hardlink':os.link(f,t/'hardlink')
  elif c=='fifo':os.mkfifo(t/'fifo')
  elif c=='recomputed_manifest_old_anchor':
   f.write_bytes(f.read_bytes()+b'\n% mutation\n');m=json.loads((t/'MANIFEST.json').read_text());m['files']['public/article.tex']={'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size};(t/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
  code,out=run(rr,anchor);ok=(code==0) if c=='positive' else (code!=0);results.append({'case':c,'expected':'PASS' if c=='positive' else 'REJECT','exit_code':code,'matched':ok,'output':out.strip()});shutil.rmtree(t)
after={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}
report={'anchor':a.anchor,'controls_outside_packet':True,'source_unchanged':before==after,'results':results,'all_passed':before==after and all(x['matched'] for x in results)}
print(json.dumps(report,indent=2));raise SystemExit(0 if report['all_passed'] else 1)
