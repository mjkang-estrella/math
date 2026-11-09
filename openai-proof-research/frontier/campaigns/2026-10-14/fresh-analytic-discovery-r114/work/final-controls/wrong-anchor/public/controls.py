#!/usr/bin/env python3
"""MIT. Copied integrity controls at an externally supplied FINAL anchor."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--expect-finalhash',required=True);ap.add_argument('--scratch',type=Path,required=True);args=ap.parse_args()
 root=args.packet.absolute();scratch=args.scratch.absolute();assert not scratch.exists();scratch.mkdir(parents=True)
 verifier=root/'public/verify.py';before={p.relative_to(root).as_posix():sha(p) for p in root.rglob('*') if p.is_file()}
 cases=['baseline','missing-anchor','wrong-anchor','changed-report','missing-file','extra-file','extra-directory','symlink','hardlink','changed-mode','changed-source','changed-primary','changed-manifest','resealed-report']
 results=[]
 for case in cases:
  d=scratch/case;shutil.copytree(root,d)
  q=d/'public/research-report.md';anchor=args.expect_finalhash
  if case=='wrong-anchor':anchor='0'*64
  elif case=='changed-report':q.write_bytes(q.read_bytes()+b'\nmutation\n')
  elif case=='missing-file':(d/'public/status.json').unlink()
  elif case=='extra-file':(d/'unexpected').write_text('unexpected')
  elif case=='extra-directory':(d/'unexpected-dir').mkdir()
  elif case=='symlink':q.unlink();q.symlink_to('radial-calculation.md')
  elif case=='hardlink':q.unlink();os.link(d/'public/radial-calculation.md',q)
  elif case=='changed-mode':q.chmod(0o600)
  elif case=='changed-source':
   x=d/'private/upstream/353/0-main.tex';x.write_bytes(x.read_bytes()+b'\nmutation')
  elif case=='changed-primary':
   x=d/'private/primary/tw2000.pdf';x.write_bytes(x.read_bytes()+b'\nmutation')
  elif case=='changed-manifest':
   x=d/'manifest.json';x.write_bytes(x.read_bytes()+b' ')
  elif case=='resealed-report':
   q.write_bytes(q.read_bytes()+b'\nmutation\n');m=json.loads((d/'manifest.json').read_text())
   for row in m['files']:
    if row['path']=='public/research-report.md':row['bytes']=q.stat().st_size;row['sha256']=sha(q)
   (d/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
  cmd=[sys.executable,str(verifier),'--packet',str(d)]
  if case!='missing-anchor':cmd+=['--expect-finalhash',anchor]
  run=subprocess.run(cmd,capture_output=True,text=True);ok=(run.returncode==0)==(case=='baseline')
  results.append(dict(case=case,expected_accept=case=='baseline',returncode=run.returncode,control_ok=ok,stdout=run.stdout.strip(),stderr=run.stderr.strip()))
 after={p.relative_to(root).as_posix():sha(p) for p in root.rglob('*') if p.is_file()}
 assert before==after,'original packet changed';assert all(x['control_ok'] for x in results),'control failed'
 print(json.dumps(dict(finalhash=args.expect_finalhash,original_packet_unchanged=True,integrity_controls_only=True,mathematical_validation=False,results=results),indent=2,sort_keys=True))
if __name__=='__main__':main()
