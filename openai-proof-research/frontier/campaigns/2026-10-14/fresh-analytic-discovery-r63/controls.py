#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Reason-checked identity mutations; only disposable /var/tmp copies change."""
import argparse,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);a=ap.parse_args();root=Path(__file__).resolve().parent
 work=Path(tempfile.mkdtemp(prefix='analytic-r63-controls-',dir='/var/tmp'));rows=[]
 def run(name,mutate,reason,accept=False,wrong=False):
  p=work/name;shutil.copytree(root,p);mutate(p)
  r=subprocess.run([sys.executable,'-B',str(p/'verify.py'),'--anchor','0'*64 if wrong else a.anchor],capture_output=True,text=True)
  text=r.stdout+r.stderr
  assert (r.returncode==0)==accept and reason in text,(name,text)
  rows.append(dict(case=name,accepted=r.returncode==0,expected_reason=reason))
 run('positive',lambda p:None,'IDENTITY PASS',True)
 run('wrong-anchor',lambda p:None,'external manifest mismatch',wrong=True)
 run('changed',lambda p:(p/'working-interface.md').write_text('changed'),'file inventory mismatch')
 run('missing',lambda p:(p/'working-interface.md').unlink(),'file inventory mismatch')
 run('extra',lambda p:(p/'extra').write_text('x'),'file inventory mismatch')
 run('extra-directory',lambda p:(p/'extra').mkdir(),'directory inventory mismatch')
 run('manifest',lambda p:(p/'manifest.json').write_text('{}'),'external manifest mismatch')
 def link(p):
  (p/'working-interface.md').unlink();(p/'working-interface.md').symlink_to(root/'working-interface.md')
 run('symlink-payload',link,'symlink entry')
 def hard(p):
  (p/'working-interface.md').unlink();os.link(p/'coefficient-lemma.md',p/'working-interface.md')
 run('hardlink',hard,'hardlink entry')
 run('fifo',lambda p:os.mkfifo(p/'fifo'),'nonregular entry')
 def rootlink(p):
  moved=p.with_name(p.name+'-real');p.rename(moved);p.symlink_to(moved,target_is_directory=True)
 run('root-symlink',rootlink,'symlink root ancestry')
 print(json.dumps(dict(status='PASS_IDENTITY_CONTROLS_ONLY',anchor=a.anchor,work_directory=str(work),results=rows),indent=2))
if __name__=='__main__':main()
