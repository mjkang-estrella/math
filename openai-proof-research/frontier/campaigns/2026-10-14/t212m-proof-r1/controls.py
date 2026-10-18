#!/usr/bin/env python3
# Adapted from fresh-analytic-discovery-r74/controls.py
# (sha256 2e0bfb4a814404f565342134f3b4f899b6da0b48f984f95e4ffb2beac579273e,
# Copyright 2026 Myeongjin Kang, MIT) for the t212m-proof-r1 review record.
"""Reason-checked identity mutations; only disposable /var/tmp copies change."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True

def remanifest(p):
 files={};dirs=[]
 for base,ds,fs in os.walk(p):
  for n in ds:dirs.append(str((Path(base)/n).relative_to(p)))
  for n in fs:
   q=Path(base)/n;r=str(q.relative_to(p))
   if r!='manifest.json':b=q.read_bytes();files[r]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 m=json.loads((p/'manifest.json').read_bytes());m['files']=files;m['directories']=sorted(dirs)
 raw=(json.dumps(m,indent=1,sort_keys=True)+'\n').encode();(p/'manifest.json').write_bytes(raw)
 return hashlib.sha256(raw).hexdigest()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);a=ap.parse_args();root=Path(__file__).resolve().parent
 packet=root.parent/json.loads((root/'checks.json').read_bytes())['reviewed_packet']
 work=Path(tempfile.mkdtemp(prefix='t212m-proof-r1-controls-',dir='/var/tmp'));rows=[]
 def run(name,mutate,reason,accept=False,wrong=False,pkt=None):
  p=work/name;shutil.copytree(root,p);given=mutate(p)
  anchor=given if isinstance(given,str) else ('0'*64 if wrong else a.anchor)
  r=subprocess.run([sys.executable,'-B',str(p/'verify.py'),'--anchor',anchor,'--packet',str(pkt or packet)],capture_output=True,text=True)
  text=r.stdout+r.stderr
  assert (r.returncode==0)==accept and reason in text,(name,text)
  rows.append(dict(case=name,accepted=r.returncode==0,expected_reason=reason))
 run('positive',lambda p:None,'IDENTITY PASS',True)
 run('wrong-anchor',lambda p:None,'external manifest mismatch',wrong=True)
 run('changed',lambda p:(p/'review.md').write_text('changed'),'file inventory mismatch')
 run('missing',lambda p:(p/'review.md').unlink(),'file inventory mismatch')
 run('extra',lambda p:(p/'extra').write_text('x'),'file inventory mismatch')
 run('extra-directory',lambda p:(p/'extra').mkdir(),'directory inventory mismatch')
 run('manifest',lambda p:(p/'manifest.json').write_text('{}'),'external manifest mismatch')
 def link(p):
  (p/'review.md').unlink();(p/'review.md').symlink_to(root/'review.md')
 run('symlink-payload',link,'symlink entry')
 def hard(p):
  (p/'review.md').unlink();os.link(p/'reading-limits.md',p/'review.md')
 run('hardlink',hard,'hardlink entry')
 run('fifo',lambda p:os.mkfifo(p/'fifo'),'nonregular entry')
 def rootlink(p):
  moved=p.with_name(p.name+'-real');p.rename(moved);p.symlink_to(moved,target_is_directory=True)
 run('root-symlink',rootlink,'symlink root ancestry')
 def inconsistent(p):
  c=json.loads((p/'checks.json').read_bytes());c['required_objections']=['R1']
  (p/'checks.json').write_text(json.dumps(c,indent=1)+'\n');return remanifest(p)
 run('pass-with-required-objection',inconsistent,'verdict inconsistency')
 def certified(p):
  c=json.loads((p/'checks.json').read_bytes());c['mathematical_verdict_certified_by_code']=True
  (p/'checks.json').write_text(json.dumps(c,indent=1)+'\n');return remanifest(p)
 run('code-certification-claim',certified,'code-certification claim')
 run('malformed-anchor',lambda p:'xyz','malformed anchor')
 alt=work/'packet-changed';shutil.copytree(packet,alt,symlinks=True)
 with open(alt/'candidate-proof.md','ab') as f:f.write(b'\n')
 run('reviewed-packet-changed',lambda p:None,'reviewed packet mismatch',pkt=alt)
 alt2=work/'packet-linked';shutil.copytree(packet,alt2,symlinks=True)
 (alt2/'cubic-wall.md').unlink();(alt2/'cubic-wall.md').symlink_to(packet/'cubic-wall.md')
 run('reviewed-packet-symlink',lambda p:None,'reviewed packet nonregular entry',pkt=alt2)
 run('reviewed-packet-missing',lambda p:None,'reviewed packet missing',pkt=work/'absent')
 print(json.dumps(dict(status='PASS_IDENTITY_CONTROLS_ONLY',anchor=a.anchor,work_directory=str(work),results=rows),indent=2))
if __name__=='__main__':main()
