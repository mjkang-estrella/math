#!/usr/bin/env python3
"""MIT. Fresh compilation and axiom audit of limited relational support."""
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
CACHE = HERE.parent / 'formal/.lake/packages'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    receipt = {'status': 'RUNNING', 'full_T259S_formalized': False,
               'independent_formal_review': False, 'count_delta': 0}
    sha = lambda b: hashlib.sha256(b).hexdigest()
    try:
        lock = json.loads((HERE/'lake-manifest.json').read_text())
        libs, pins = [], {}
        for e in lock['packages']:
            p = CACHE/e['name']
            actual = subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
            assert actual == e['rev'], e['name']
            assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],text=True).strip()
            pins[e['name']] = actual
            if (p/'.lake/build/lib/lean').is_dir(): libs.append(str(p/'.lake/build/lib/lean'))
        version = subprocess.check_output([str(LEAN),'--version'],text=True).strip()
        assert '4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version
        receipt.update(lean_version=version, lean_binary_sha256=sha(LEAN.read_bytes()), dependencies=pins)
        declarations, source_hashes = [], {}
        for name, ns in [('Propagation','T259S'),('Controls','T259SControls')]:
            raw = (HERE/(name+'.lean')).read_bytes(); code = raw.decode()
            assert not re.search(r'\b(?:sorry|admit|unsafe|native_decide)\b|^\s*axiom\s',code,re.M)
            source_hashes[name+'.lean'] = sha(raw)
            declarations += [ns+'.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',code,re.M)]
        receipt['sources'] = source_hashes
        with tempfile.TemporaryDirectory(prefix='t259s-scoped-build-',dir='/var/tmp') as td:
            build = Path(td); env = os.environ.copy();env['LEAN_PATH'] = os.pathsep.join([str(build)]+libs)
            for name in ['Propagation','Controls']: shutil.copyfile(HERE/(name+'.lean'),build/(name+'.lean'))
            audit = 'import Controls\n'+'\n'.join('#check @'+n+'\n#print axioms '+n for n in declarations)+'\n'
            (build/'Audit.lean').write_text(audit); (out/'Audit.lean').write_text(audit)
            for name, argv in [('propagation',['-o','Propagation.olean','Propagation.lean']),
                               ('controls',['-o','Controls.olean','Controls.lean']),('audit',['Audit.lean'])]:
                p = subprocess.run([str(LEAN)]+argv,cwd=build,env=env,capture_output=True,text=True)
                output = p.stdout+p.stderr;(out/(name+'.log')).write_text(output)
                assert p.returncode == 0 and not re.search(r'\b(?:error|warning):',output),output
            text = (out/'audit.log').read_text(); reports = {}
            for n in declarations:
                m = re.search("'"+re.escape(n)+r"' depends on axioms: \[([^\]]*)\]",text)
                if m: used = set(m.group(1).split(', ')) - {''}
                else:
                    assert "'"+n+"' does not depend on any axioms" in text,n
                    used = set()
                assert used <= {'propext','Classical.choice','Quot.sound'}, (n,used)
                reports[n] = sorted(used)
            receipt.update(status='PASS_SCOPED_RELATIONAL_SUPPORT',kernel_dependencies=reports)
    except Exception as e:
        receipt.update(status='FAILED',error=str(e));raise
    finally: (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status'])

if __name__ == '__main__': main()
