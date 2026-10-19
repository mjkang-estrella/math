#!/usr/bin/env python3
"""Independent copied build and deliberately broken proof sensitivity checks.

Offline, read-only on compiler/cache/author input. Does not rebuild mathlib.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--cache', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    a.lean = a.lean.resolve()
    a.cache = a.cache.resolve()
    out = a.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = HERE / 'copied-author'
    pins, libs = {}, []
    for entry in json.loads((source/'lake-manifest.json').read_text())['packages']:
        dep = a.cache / entry['name']
        actual = subprocess.check_output(['git','-C',str(dep),'rev-parse','HEAD'], text=True).strip()
        assert actual == entry['rev'], entry['name']
        assert not subprocess.check_output(['git','-C',str(dep),'status','--porcelain','--untracked-files=no'], text=True).strip()
        pins[entry['name']] = actual
        lib = dep/'.lake/build/lib/lean'
        if lib.is_dir(): libs.append(str(lib.resolve()))
    version = subprocess.check_output([str(a.lean),'--version'], text=True).strip()
    assert '4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version
    receipt = dict(full_theorem_formalized=False, network_used=False,
                   independent_review=True, trusted_preexisting_dependency_oleans=True,
                   lean_version=version, lean_binary_sha256=sha(a.lean), dependencies=pins,
                   sources={}, runs=[], expected_rejections=[])
    declarations=[]
    for name, namespace, path in [('T298P.lean','T298P',source/'T298P.lean'),
                                  ('Controls.lean','T298PControls',source/'Controls.lean'),
                                  ('Independent.lean','T298PReview',HERE/'Independent.lean')]:
        code = path.read_text()
        assert not re.search(r'\b(?:sorry|admit|unsafe|native_decide)\b|^\s*axiom\s',code,re.M)
        receipt['sources'][name]=sha(path)
        declarations += [namespace+'.'+n for n in re.findall(r'^theorem (\w+)',code,re.M)]
    with tempfile.TemporaryDirectory(prefix='t298p-review-build-') as temp:
        build=Path(temp)
        env=os.environ.copy(); env['LEAN_PATH']=os.pathsep.join([str(build)]+libs)
        for name,path in [('T298P.lean',source/'T298P.lean'),('Controls.lean',source/'Controls.lean'),('Independent.lean',HERE/'Independent.lean')]:
            (build/name).write_bytes(path.read_bytes())
        def run(label, argv, reject=False):
            p=subprocess.run([str(a.lean),*argv],cwd=build,env=env,capture_output=True,text=True)
            log=p.stdout+p.stderr; (out/(label+'.log')).write_text(log)
            row=dict(step=label,exit_code=p.returncode,output_sha256=hashlib.sha256(log.encode()).hexdigest())
            if reject:
                assert p.returncode != 0 and 'error:' in log, label
                receipt['expected_rejections'].append(row)
            else:
                assert p.returncode == 0 and not re.search(r'\b(?:error|warning):',log), (label,log)
                receipt['runs'].append(row)
            return log
        for module in ['T298P','Controls','Independent']:
            run(module,['-o',module+'.olean',module+'.lean'])
        checks='import T298P\nimport Controls\nimport Independent\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in declarations)
        (build/'Checks.lean').write_text(checks);(out/'Checks.lean').write_text(checks)
        log=run('types-axioms',['Checks.lean'])
        reports={}
        for n in declarations:
            m=re.search("'"+re.escape(n)+r"' depends on axioms: \[([^\]]*)\]",log)
            assert m,n
            axioms=set(re.split(r',\s*',m.group(1)))-{''}
            assert axioms <= STANDARD,(n,axioms)
            reports[n]=sorted(axioms)
        receipt['kernel_dependencies']=reports
        original=(source/'T298P.lean').read_text()
        coefficient=original.split('theorem leading_score_energy')[0]+'end\nend T298P\n'
        transfer='import Mathlib.Tactic\nnamespace T298P\ntheorem gap_transfer'+original.split('theorem gap_transfer')[1].split('theorem strict_gap')[0]
        transfer+='end T298P\n'
        mutations={
          'denominator-k2':original.replace('(epsilon^2 * k^4)', '(epsilon^2 * k^2)'),
          'no-column-gram':coefficient.replace('(hC : ∀ a b, ∑ q, C q a * C q b = if a = b then 1 else 0)', '').replace('simp [hC]', 'simp'),
          'no-endpoint':transfer.replace('(comparison : micro1 ≤ star1)', ''),
          'reversed-gap':transfer.replace('((sourceStar0 - sourceMicro0) - (sourceStar1 - sourceMicro1))', '((sourceStar1 - sourceMicro1) - (sourceStar0 - sourceMicro0))'),
          'weak-error':original.replace('(errors : eMicro + eStar <', '(errors : eMicro + eStar ≤')
        }
        for label,code in mutations.items():
            assert code != original
            (build/'Mutation.lean').write_text(code)
            (out/(label+'.lean')).write_text(code)
            run(label,['Mutation.lean'],reject=True)
    receipt['status']='PASS_INDEPENDENT_SCOPED_AUDIT_BUILD_AND_SENSITIVITY'
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status'])
    print(f'{len(declarations)} theorem types/axioms checked; {len(mutations)} expected rejections')

if __name__=='__main__': main()
