#!/usr/bin/env python3
"""MIT, Myeongjin Kang. Recompile scoped kinetic algebra from source."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile
HERE=Path(__file__).resolve().parent

def main():
    lean=shutil.which('lean');lake=shutil.which('lake')
    if not lean or not lake:raise RuntimeError('Put the pinned Lean 4.34.1 bin directory on PATH.')
    version=subprocess.check_output([lean,'--version'],text=True).strip()
    assert '4.34.1' in version
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=HERE/'.lake/packages/mathlib',text=True).strip()
    assert revision=='d13f23b723b8a846827a245b89c10fc7d3f11612'
    source=(HERE/'KineticSupport.lean').read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
    paths=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=HERE,text=True).strip().split(os.pathsep)
    paths=[str((HERE/p).resolve()) if not Path(p).is_absolute() else p for p in paths]
    runs=[]
    (HERE/'logs').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='kinetic-lean-') as directory:
        temp=Path(directory)
        for name in ['KineticSupport.lean','Checks.lean']:shutil.copy2(HERE/name,temp/name)
        env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(temp)]+paths)
        for label,args in [('source',[lean,'-o','KineticSupport.olean','KineticSupport.lean']),('types-and-axioms',[lean,'Checks.lean'])]:
            run=subprocess.run(args,cwd=temp,env=env,text=True,capture_output=True)
            output=run.stdout+run.stderr;(HERE/'logs'/f'{label}.txt').write_text(output)
            assert run.returncode==0,output
            assert 'warning:' not in output and 'sorryAx' not in output,output
            if label=='types-and-axioms':
                axiom_lists=re.findall(r'depends on axioms: \[([^\]]*)\]',output)
                assert len(axiom_lists)==9,output
                for row in axiom_lists:
                    assert set(row.split(', ')) <= {'propext','Classical.choice','Quot.sound'},row
            runs.append({'check':label,'exit_code':run.returncode,'warnings':0})
    result={'status':'compiled supporting algebra','theorems':9,'source_sha256':hashlib.sha256((HERE/'KineticSupport.lean').read_bytes()).hexdigest(),'toolchain':version,'mathlib':revision,'checks':runs,'author_olean_trusted':False,'scope':'Elastic pair momentum/energy, finite all-line energy under pair replacement, affine common-time-shift algebra, exact rational exponent budget. No construction of hard-sphere histories, probability estimates, tightness or path-limit formalization.','independent_semantic_review':False,'count_credit':0,'dependency_cache':'Existing pinned campaign cache reused; no fresh network installation tested.'}
    (HERE/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
