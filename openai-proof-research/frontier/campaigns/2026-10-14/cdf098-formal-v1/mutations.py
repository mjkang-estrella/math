#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Fresh proof rejection controls."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib,json,os,re,subprocess,tempfile
from pathlib import Path
from rebuild import HERE,DEFAULT_LEAN,DEFAULT_CACHE,LEAN_COMMIT

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',type=Path,default=DEFAULT_LEAN)
    ap.add_argument('--cache',type=Path,default=DEFAULT_CACHE)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    out=(HERE/(args.output or Path('.replays')/('mutations-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')))).resolve()
    if not out.is_relative_to(HERE) or out==HERE: raise ValueError('Output must be a new package subdirectory')
    out.mkdir(parents=True,exist_ok=False)
    lock=json.loads((HERE/'lake-manifest.json').read_text());libs=[]
    for entry in lock['packages']:
        dep=args.cache/entry['name']
        actual=subprocess.check_output(['git','-C',str(dep),'rev-parse','HEAD'],text=True).strip()
        if actual!=entry['rev']: raise ValueError('Dependency pin mismatch')
        lib=dep/'.lake/build/lib/lean'
        if lib.is_dir(): libs.append(str(lib.resolve()))
    version=subprocess.check_output([str(args.lean),'--version'],text=True)
    if '4.34.1' not in version or LEAN_COMMIT not in version: raise ValueError('Compiler mismatch')
    source=(HERE/'CDFLocal.lean').read_text()
    cases=[
      ('recenter-factor-one','recenter_pullback','packing_bound','2*K*r','K*r',2),
      ('weak-packing-separation','packing_bound','doubling_packing','s < dist x y','s ≤ dist x y',1),
      ('widened-dyadic-window','dyadic_window_card','intermediate_scale_count','(hwidth : U ≤ (2:ℝ)^q*L)','(hwidth : U ≤ (2:ℝ)^(q+1)*L)',1),
      ('fine-radius-too-small','fine_edge_bound','cluster_separation','d < r/16','d < r/64',1),
      ('cluster-constant-too-large','cluster_separation','meeting_cluster_scale','(97/200 : ℝ)*a','(1/2 : ℝ)*a',1),
      ('low-count-too-small','low_count','high_count','≤ 81*D^10','≤ 80*D^10',1)]
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(libs)
    def run(case):
        label,target,next_name,old,new,count=case
        start=source.index('theorem '+target)
        cut=source.index('theorem '+next_name)
        doc=source.rfind('/--',start,cut)
        if doc!=-1 and source[doc:cut].strip().endswith('-/'):
            cut=doc
        selected=source[start:cut]
        if selected.count(old)!=count: raise ValueError('Mutation target is not unique: '+label)
        body=source[:start]+selected.replace(old,new)+'end CDFLocal\n'
        with tempfile.TemporaryDirectory(prefix='.mutation-',dir=HERE) as directory:
            f=Path(directory)/'Mutation.lean';f.write_text(body)
            result=subprocess.run([str(args.lean),'Mutation.lean'],cwd=directory,env=env,capture_output=True,text=True,timeout=300)
        (out/(label+'.stdout')).write_text(result.stdout);(out/(label+'.stderr')).write_text(result.stderr)
        text=result.stdout+result.stderr
        proof_failure=('linarith failed' in text or 'unsolved goals' in text or 'omega could not prove' in text)
        invalid=any(x in text for x in ['unknown module','unexpected token','Unknown identifier','Type mismatch','Application type mismatch'])
        if result.returncode==0 or not proof_failure or invalid: raise AssertionError(label+' did not yield mathematical proof rejection: '+text)
        return dict(case=label,result='EXPECTED_PROOF_REJECTION',exit_code=result.returncode,
                    mutant_sha256=hashlib.sha256(body.encode()).hexdigest(),
                    stdout_sha256=hashlib.sha256(result.stdout.encode()).hexdigest())
    with ThreadPoolExecutor(max_workers=2) as pool: results=list(pool.map(run,cases))
    receipt=dict(status='PASS six false variants rejected by Lean',source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                 compiler=version.strip(),cases=results,full_CDF098_formalized=False)
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt['status'])

if __name__=='__main__': main()
