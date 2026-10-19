#!/usr/bin/env python3
"""Parent replay on disposable copies; no mathematical gate."""
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(root):
    result={}
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat(); value=[s.st_mode,s.st_nlink]
        if stat.S_ISREG(s.st_mode): value += [s.st_size,sha(p)]
        elif stat.S_ISLNK(s.st_mode): value += [os.readlink(p)]
        result[p.relative_to(root).as_posix()]=value
    return result

def run(args):
    p=subprocess.run(args,capture_output=True,text=True)
    if p.returncode: raise RuntimeError(p.stderr or p.stdout)
    return json.loads(p.stdout)

def main():
    parent=Path(__file__).resolve().parent
    campaign=parent.parent
    project=campaign.parents[2]
    arithmetic=parent.name=='discovery-arithmetic-r90-parent'
    if arithmetic:
        author=campaign/'fresh-arithmetic-discovery-r90'
        fh='26a08ebb1610413621349c7610869453b2f4774b9599a8e4a7dec191c153d68f'
        rh='3380d58b20015a4f01d2d054c733db26ae4a800f6aaefeb637c19a7770bdf415'
        options=['--finalhash',fh,'--reporthash',rh,'--canonical-tree',str(project/'sources/preprints-tree.json')]
    else:
        author=campaign/'fresh-analytic-discovery-r125'
        fh='4ac4ced51a717dbcf0005c57f692bfad59eb64f8d58069d2c4cbb98b298ccb83'
        rh='79634fc0da9e1c99303b26e69c72d64191cdc6e0952e341ebf0b9581d188beba'
        options=['--final-sha256',fh,'--report-sha256',rh]
    assert sha(author/'FINAL.json')==fh and sha(author/'REPORT.md')==rh
    tree=project/'sources/preprints-tree.json'
    assert sha(tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    original=snapshot(author)
    verification=run([sys.executable,'-B',str(author/'packet/public/verify.py'),'--root',str(author)]+options)
    with tempfile.TemporaryDirectory(prefix='.replay-',dir=parent) as tmp:
        work=Path(tmp); copy=work/'author'
        shutil.copytree(author,copy,symlinks=True)
        assert snapshot(copy)==original
        if arithmetic:
            controls=run([sys.executable,'-B',str(copy/'packet/public/control_checks.py'),'--root',str(copy)]+options)
            controls=json.loads((copy/'integrity-results.json').read_text())
            assert controls['cases_expected']==18 and controls['original_unchanged']
            assert all(x['expected'] and x['copied_inputs_unchanged'] for x in controls['cases'])
        else:
            (copy/'work').mkdir(exist_ok=True)
            source=(copy/'packet/public/controls.py').read_text()
            definition="""def full_snapshot(root):
 out={}
 for p in [root]+sorted(root.rglob('*')):
  s=p.lstat();v=[s.st_mode,s.st_nlink]
  if stat.S_ISREG(s.st_mode):v += [s.st_size,hashlib.sha256(p.read_bytes()).hexdigest()]
  elif stat.S_ISLNK(s.st_mode):v += [os.readlink(p)]
  out[p.relative_to(root).as_posix()]=v
 return out
"""
            source=source.replace('import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile','import argparse,hashlib,json,os,shutil,stat,subprocess,sys,tempfile')
            source=source.replace('def main():',definition+'\ndef main():',1)
            token='   p=subprocess.run(cmd,capture_output=True,text=True);want='
            assert source.count(token)==1
            source=source.replace(token,"   copied_before=full_snapshot(c)\n   p=subprocess.run(cmd,capture_output=True,text=True)\n   copied_unchanged=full_snapshot(c)==copied_before\n   assert copied_unchanged, name\n   want=")
            source=source.replace('   shutil.rmtree(c)',"   results[-1]['copied_inputs_unchanged']=copied_unchanged\n   shutil.rmtree(c)")
            helper=work/'instrumented_controls.py';helper.write_text(source)
            controls=run([sys.executable,'-B',str(helper),'--root',str(copy)]+options)
            assert controls['all_expected'] and len(controls['cases'])==18
            assert all(x['copied_inputs_unchanged'] for x in controls['cases'])
    assert snapshot(author)==original
    result={'status':'INTEGRITY_ONLY','detached_final_sha256':fh,'detached_report_sha256':rh,
            'author_manifest_sha256':sha(author/'packet/MANIFEST.json'),
            'verification':verification,'controls':controls,'whole_actual_author_root_unchanged':True,
            'parent_instrumentation':False if arithmetic else 'Outside-copy derivative control runner adds full per-copy bytes/modes/link-count snapshots; selected FINAL-bound runner and copied verifier remain unmodified.',
            'scope_limits':'Artifact controls only. No independent mathematical or contribution verdict. No hostile-code sandbox/race guarantee. Analytic packet does not seal permission modes/hardlink counts; preservation is separately compared.'}
    (parent/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'parent':parent.name,'cases':len(controls['cases']),'whole_actual_author_root_unchanged':True,'verification':verification}))

if __name__=='__main__':main()
