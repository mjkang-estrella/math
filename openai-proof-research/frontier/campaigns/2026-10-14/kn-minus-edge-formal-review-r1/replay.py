#!/usr/bin/env python3
"""Fresh replay to a new review-owned directory without resealing evidence.
Copyright 2026 Myeongjin Kang; MIT.
"""
from pathlib import Path
import argparse,datetime,hashlib,json,os,shutil,subprocess
H=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--output',type=Path,help='new directory inside this review (default .replays/timestamp)')
 args=p.parse_args()
 # Read-only verification precedes any replay writes.
 subprocess.run(['python3','-B',str(H/'verify_review.py')],check=True)
 receipt=json.loads((H/'build-receipt.json').read_text());lean=Path(receipt['compiler_realpath'])
 assert hashlib.sha256(lean.read_bytes()).hexdigest()==receipt['compiler']['sha256']
 out=(args.output or H/'.replays'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')).resolve()
 assert out.is_relative_to(H) and out!=H
 out.mkdir(parents=True,exist_ok=False)
 cache=H.parent/'formal/.lake/packages';lock=json.loads((H.parent/'kn-minus-edge-formal-v1/lake-manifest.json').read_text())
 libs=[];env=os.environ.copy();env['GIT_OPTIONAL_LOCKS']='0';env['PYTHONDONTWRITEBYTECODE']='1'
 for pkg in lock['packages']:
  d=cache/pkg['name'];rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],env=env,text=True).strip()
  assert rev==pkg['rev']
  assert not subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],env=env,text=True)
  lib=d/'.lake/build/lib/lean'
  if lib.is_dir():libs.append(str(lib.resolve()))
 env['LEAN_PATH']=os.pathsep.join([str(out)]+libs)
 # Only source copies, never preexisting support objects.
 for f in ['KnMinusEdge.lean','Controls.lean','Checks.lean','ControlChecks.lean','ReviewControls.lean','ReviewQueries.lean','ReadableQueries.lean']:
  shutil.copyfile(H/'build'/f,out/f)
 author=H.parent/'kn-minus-edge-formal-v1'
 for f in ['checked_run.py','semantic_checks.py']:shutil.copyfile(author/f,out/f)
 runs=[]
 steps=[('version',['--version']),('core',['-o','KnMinusEdge.olean','KnMinusEdge.lean']),('author-controls',['-o','Controls.olean','Controls.lean']),('review-controls',['-o','ReviewControls.olean','ReviewControls.lean']),('author-types',['Checks.lean']),('author-control-types',['ControlChecks.lean']),('review-types',['ReviewQueries.lean']),('all-readable-types',['ReadableQueries.lean'])]
 for name,cmd in steps:
  proc=subprocess.run([str(lean),*cmd],cwd=out,env=env,text=True,capture_output=True)
  (out/f'{name}.stdout').write_text(proc.stdout);(out/f'{name}.stderr').write_text(proc.stderr)
  runs.append({'label':name,'exit_code':proc.returncode,'command':[str(lean),*cmd]})
  (out/'receipt.json').write_text(json.dumps({'runs':runs,'status':'RUNNING'},indent=2)+'\n')
  assert proc.returncode==0,(name,proc.stdout,proc.stderr)
  print(name,'PASS',flush=True)
 proc=subprocess.run(['python3','-B','semantic_checks.py'],cwd=out,env=env,text=True,capture_output=True)
 (out/'arithmetic.stdout').write_text(proc.stdout);(out/'arithmetic.stderr').write_text(proc.stderr);assert proc.returncode==0
 (out/'receipt.json').write_text(json.dumps({'runs':runs,'arithmetic_exit':proc.returncode,'status':'PASS','full_crossing_certificate':False},indent=2)+'\n')
 print('PASS new replay:',out)
if __name__=='__main__':main()
