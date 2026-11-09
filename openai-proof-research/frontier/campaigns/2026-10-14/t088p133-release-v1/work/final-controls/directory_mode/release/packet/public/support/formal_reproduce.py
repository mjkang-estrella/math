#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Relative reproduction of unchanged reviewed support; dependencies supplied explicitly.
Only copied package sources are built, under this manuscript root's build/work/.
Historical inventories/replay.py are provenance, never execution dependencies.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, importlib.util
from pathlib import Path
sys.dont_write_bytecode = True
PUBLIC = Path(__file__).resolve().parents[1]
ROOT = PUBLIC.parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
def require(ok, msg):
    if not ok: raise ValueError(msg)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--cache', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True, help='fresh path under manuscript-root/build/work')
    a=ap.parse_args(); out=a.output.resolve(); lean=a.lean.resolve(); cache=a.cache.resolve()
    require(out.is_relative_to((ROOT/'build/work').resolve()), 'output outside manuscript-root/build/work')
    require(not out.exists(), 'use a fresh output directory')
    out.mkdir(parents=True)
    result={'scope':'Reproduction of previously reviewed deterministic algebra only; no new review gate',
            'full_theorem_formalized':False, 'commands':[], 'source_hashes':{},
            'trust':'Supplied Lean and precompiled dependencies; no clean-source dependency build or complete binary-cache authentication'}
    def run(argv,cwd,label,env=None,success=True):
        cp=subprocess.run(list(map(str,argv)),cwd=cwd,env=env,text=True,capture_output=True)
        log=cp.stdout+cp.stderr;(out/(label+'.log')).write_text(log)
        result['commands'].append({'label':label,'argv':list(map(str,argv)),'exit':cp.returncode,'log_sha256':sha(out/(label+'.log'))})
        if success: require(cp.returncode==0 and not re.search(r'\b(?:error|warning):',log),'failed/warned '+label)
        return cp,log
    try:
        origins=json.loads((PUBLIC/'formal/origin.json').read_text())
        files=['T088P133.lean','Controls.lean','rebuild.py','lean-toolchain','lake-manifest.json']
        package=out/'package'; source=package/'packet/public';source.mkdir(parents=True)
        for f in files:
            rel='formal/implementation/'+f;src=PUBLIC/rel
            require(sha(src)==origins[rel]['sha256'],'reviewed origin mismatch '+f)
            shutil.copy2(src,source/f);result['source_hashes'][rel]=sha(src)
        for f in ['SemanticAudit.lean','exact_controls.py']:
            rel='formal/review/'+f;require(sha(PUBLIC/rel)==origins[rel]['sha256'],'reviewed origin mismatch '+f)
            result['source_hashes'][rel]=sha(PUBLIC/rel)
        build=package/'work/fresh'
        run([sys.executable,'-B',source/'rebuild.py','--output',build,'--lean',lean,'--cache',cache],package,'implementation-build')
        receipt=json.loads((build/'receipt.json').read_text());result['implementation_receipt']=receipt
        require([len(v) for v in receipt['declarations'].values()]==[21,20],'implementation declaration counts')
        env=os.environ.copy();env.update(receipt['environment']);env['PYTHONDONTWRITEBYTECODE']='1'
        shutil.copy2(PUBLIC/'formal/review/SemanticAudit.lean',build/'SemanticAudit.lean')
        code=(build/'SemanticAudit.lean').read_text()
        require(not re.search(r'\b(?:sorry|admit|unsafe|native_decide)\b|^\s*axiom\s',code,re.M),'audit proof escape')
        run([lean,'-o','SemanticAudit.olean','SemanticAudit.lean'],build,'semantic-build',env)
        names=['T088P133Review.'+n for n in re.findall(r'^theorem (\w+)',code,re.M)]
        require(len(names)==15,'review declaration count')
        driver='import SemanticAudit\nset_option pp.universes false\n'
        driver+=''.join('#print T088P133.'+n+'\n' for n in ['firstBracket','secondBracket','mixture'])
        driver+=''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names)
        (build/'ReviewChecks.lean').write_text(driver)
        _,log=run([lean,'ReviewChecks.lean'],build,'review-types-axioms',env)
        axioms={}
        for n in names:
            m=re.search("'"+re.escape(n)+r"' depends on axioms: \[([^\]]*)\]",log)
            require(m is not None,'missing axiom report '+n)
            xs=set(m.group(1).split(', '));require(xs<=STANDARD,'unexpected axioms '+n);axioms[n]=sorted(xs)
        result['review_axioms']=axioms
        for f in ['types-axioms.log','support.log','controls.log']:
            shutil.copy2(build/f,out/f)
            require((build/f).read_bytes()==(PUBLIC/'formal/implementation/validation'/f).read_bytes(),'historical implementation log mismatch '+f)
        require(log==(PUBLIC/'formal/review/evidence/review-types-axioms.log').read_text(),'historical review type-log mismatch')
        result['historical_type_logs_byte_identical']=True
        spec=importlib.util.spec_from_file_location('review_exact',PUBLIC/'formal/review/exact_controls.py')
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        result['exact_configurations']=module.check()
        # Repeat the original two bounded added-premise mutations, only on fresh copies.
        source_code=(build/'T088P133.lean').read_text()
        mutations=[('strict_extra_d_positive','    (hPm : 2*d*p^2 < P) (hNm : 2*d*q^2 ≤ N) :',
          '    (hPm : 2*d*p^2 < P) (hNm : 2*d*q^2 ≤ N) (_extra : 0 < d) :','strict_interface'),
         ('nonstrict_extra_slack','    (hPm : 2*d*p^2 ≤ P) (hNm : 2*d*q^2 ≤ N) :',
          '    (hPm : 2*d*p^2 ≤ P) (hNm : 2*d*q^2 ≤ N) (_extra : (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) ≤ 1) :','nonstrict_interface')]
        result['semantic_mutations']=[]
        for label,old,new,decl in mutations:
            require(source_code.count(old)==1,'nonunique mutation')
            d=out/label;d.mkdir();(d/'T088P133.lean').write_text(source_code.replace(old,new))
            start=code.index('theorem '+decl+' :');end=code.index('\n',code.index(':= @',start))
            (d/'Contract.lean').write_text('import T088P133\nopen T088P133\n'+code[start:end]+'\n')
            menv=env.copy();menv['LEAN_PATH']=str(d)+os.pathsep+os.pathsep.join(env['LEAN_PATH'].split(os.pathsep)[1:])
            run([lean,'-o','T088P133.olean','T088P133.lean'],d,label+'-support',menv)
            cp,err=run([lean,'Contract.lean'],d,label+'-contract',menv,False)
            require(cp.returncode!=0 and 'Type mismatch' in err,'mutation not rejected by exact contract')
            result['semantic_mutations'].append({'case':label,'support_compiled':True,'contract_rejected':True})
        result.update(status='REPRODUCED_56_DECLARATIONS',support=21,controls=20,audit=15)
        print((out/'types-axioms.log').read_text(),end='')
        print(log,end='')
        print(json.dumps({'status':result['status'],'support':21,'controls':20,'audit':15,'standard_axioms':sorted(STANDARD),'semantic_mutations':2,'exact_configurations':len(result['exact_configurations'])}))
    except Exception as error:
        result.update(status='FAILED',error=str(error));raise
    finally:
        (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__': main()
