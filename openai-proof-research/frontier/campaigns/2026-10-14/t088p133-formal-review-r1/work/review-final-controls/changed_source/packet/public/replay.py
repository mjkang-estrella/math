#!/usr/bin/env python3
"""Independent copied-package formal replay. Original review code MIT, 2026 Myeongjin Kang.
Uses the separately anchored implementation's reviewed MIT build/verifier scripts.
No git, network, dependency rebuild, or writes outside this review's work/.
"""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,tarfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
BASE=PROJECT/'frontier/campaigns/2026-10-14'
IMPL=BASE/'t088p133-formal-v1'
ANCHORS={'FINAL.json':'4fa662b09a569b1120f1fe524e6f7b8d81db0cdd6b021eef8027b1622ab15964',
 'packet/MANIFEST.json':'042edffc552a51b2c5a96cfdfca660de9ced1d2295106765f292dc546dd8210a',
 'REPORT.md':'7c169c608cce6f452cf95ddee16ea1cc37fab8633d474d67d63e82245cdf1476'}
ARCHIVE='555e29786e1cf9a665036d639c3c28756a688e167f378d8bc68cbe29fe0bcc5f'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def require(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--cache',type=Path,required=True);ap.add_argument('--lean',type=Path,required=True)
 ap.add_argument('--existing-build',type=Path,help='Use the already completed first review build; ordinary replay omits this.')
 a=ap.parse_args();out=a.output.resolve();require(out.is_relative_to(ROOT/'work'),'output outside review work')
 out.mkdir(parents=True,exist_ok=False)
 result={'scope':'independent deterministic formal-support replay only','commands':[]}
 def run(cmd,cwd=None,env=None,label='command',success=True):
  x=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,text=True,capture_output=True)
  log=x.stdout+x.stderr;(out/(label+'.log')).write_text(log)
  result['commands'].append({'label':label,'argv':list(map(str,cmd)),'cwd':str(cwd),'exit':x.returncode,'log_sha256':hashlib.sha256(log.encode()).hexdigest()})
  if success:require(x.returncode==0 and not re.search(r'\b(?:error|warning):',log),'failed/warned '+label)
  return x,log
 for rel,h in ANCHORS.items():require(sha(IMPL/rel)==h,'implementation anchor '+rel)
 require(sha(IMPL/'work/t088p133-formal-v1-source.tar.gz')==ARCHIVE,'archive anchor')
 inv=module('inventory_review',HERE/'inventory.py');before=inv.snapshot()
 v=module('implementation_verifier',IMPL/'packet/public/verify.py')
 result['implementation_verified']=v.verify(IMPL,*ANCHORS.values(),PROJECT)
 if a.existing_build:
  b=a.existing_build.resolve();require(b.is_relative_to(ROOT/'work'),'existing build outside review')
  copy=b.parents[1];result['build_reused_first_fresh_invocation']=True
 else:
  copy=out/'extracted';copy.mkdir()
  with tarfile.open(IMPL/'work/t088p133-formal-v1-source.tar.gz') as t:
   names=[]
   for m in t.getmembers():
    p=Path(m.name);require(not p.is_absolute() and '..' not in p.parts and (m.isfile() or m.isdir()) and p.parts[0] in {'FINAL.json','REPORT.md','packet'},'unsafe archive entry')
    names.append(m.name)
   require(len(names)==len(set(names)),'duplicate archive paths');t.extractall(copy,filter='data')
  b=copy/'work/fresh'
  run([sys.executable,'-B',copy/'packet/public/rebuild.py','--output',b,'--cache',a.cache,'--lean',a.lean],label='implementation-build')
 result['extracted_verified']=v.verify(copy,*ANCHORS.values())
 receipt=json.loads((b/'receipt.json').read_text());require(receipt['status']=='COMPILED_SCOPED_SUPPORT_AND_CONTROLS_STANDARD_AXIOMS_ONLY','build receipt')
 require(all(x['exit_code']==0 for x in receipt['runs']),'build exits')
 for label in ['support','controls']:require((b/(label+'.log')).read_text()=='','implementation warning/error')
 for f,h in receipt['sources'].items():require(sha(b/f)==h==sha(IMPL/'packet/public'/f),'built source mismatch')
 original=json.loads((IMPL/'packet/public/validation/receipt.json').read_text())
 for key in ['sources','dependencies','lean_version','lean_binary_sha256','dependency_lock_sha256','declarations','kernel_dependencies']:require(receipt[key]==original[key],'receipt mismatch '+key)
 require(sha(b/'types-axioms.log')==sha(IMPL/'packet/public/validation/types-axioms.log'),'type log mismatch')
 result['fresh_build_receipt']=receipt
 env=os.environ.copy();env.update(receipt['environment'])
 shutil.copy2(HERE/'SemanticAudit.lean',b/'SemanticAudit.lean')
 run([a.lean,'-o','SemanticAudit.olean','SemanticAudit.lean'],cwd=b,env=env,label='semantic-build')
 names=re.findall(r'^theorem (\w+)',(HERE/'SemanticAudit.lean').read_text(),re.M)
 driver='import SemanticAudit\nset_option pp.universes false\n'
 driver+=''.join('#print T088P133.'+n+'\n' for n in ['firstBracket','secondBracket','mixture'])
 driver+=''.join('#check @T088P133Review.'+n+'\n#print axioms T088P133Review.'+n+'\n' for n in names)
 (b/'ReviewChecks.lean').write_text(driver)
 _,log=run([a.lean,'ReviewChecks.lean'],cwd=b,env=env,label='review-types-axioms')
 ax={}
 for n in names:
  key='T088P133Review.'+n
  m=re.search("'"+key+r"' depends on axioms: \[([^\]]*)\]",log)
  require(m is not None,'missing review axiom '+n);xs=set(m.group(1).split(', '));require(xs<=STANDARD,'unexpected review axiom');ax[key]=sorted(xs)
 result['review_declarations']=ax
 # Two compiled interface mutations: both add an unrequested condition without changing proofs.
 # Compile support alone, then require the independently fixed exact interface to reject it.
 mutation_results=[]
 source=(b/'T088P133.lean').read_text()
 mutations=[('strict_extra_d_positive','    (hPm : 2*d*p^2 < P) (hNm : 2*d*q^2 ≤ N) :',
   '    (hPm : 2*d*p^2 < P) (hNm : 2*d*q^2 ≤ N) (_extra : 0 < d) :','strict_interface'),
  ('nonstrict_extra_slack','    (hPm : 2*d*p^2 ≤ P) (hNm : 2*d*q^2 ≤ N) :',
   '    (hPm : 2*d*p^2 ≤ P) (hNm : 2*d*q^2 ≤ N) (_extra : (1+d)*(p*α/(α+P/p)+q*β/(β+N/q)) ≤ 1) :','nonstrict_interface')]
 for name,old,new,decl in mutations:
  require(source.count(old)==1,'mutation target not unique');d=out/name;d.mkdir();(d/'T088P133.lean').write_text(source.replace(old,new))
  text=(HERE/'SemanticAudit.lean').read_text();start=text.index('theorem '+decl+' :');end=text.index('\n',text.index(':= @',start))
  (d/'Contract.lean').write_text('import T088P133\nopen T088P133\n'+text[start:end]+'\n')
  menv=env.copy();menv['LEAN_PATH']=str(d)+os.pathsep+os.pathsep.join(env['LEAN_PATH'].split(os.pathsep)[1:])
  run([a.lean,'-o','T088P133.olean','T088P133.lean'],cwd=d,env=menv,label=name+'-support')
  x,err=run([a.lean,'Contract.lean'],cwd=d,env=menv,label=name+'-contract',success=False)
  require(x.returncode!=0 and 'Type mismatch' in err,'semantic mutation not rejected for expected reason')
  mutation_results.append({'case':name,'support_compiled':True,'contract_rejected':True,'reason':'Type mismatch: added unrequested explicit premise'})
 result['semantic_mutations']=mutation_results
 exact=module('exact_review',HERE/'exact_controls.py');result['exact_controls']=exact.check()
 args=[]
 for name,h in zip(['final','manifest','report'],ANCHORS.values()):args+=['--'+name+'-sha256',h]
 # Reuse controls already executed in the first fresh extraction; replay creates fresh ones.
 controls=copy/'work/reviewer-artifact-controls'
 if not (a.existing_build and controls.exists()):
  controls=copy/'work/replay-artifact-controls'
  run([sys.executable,'-B',copy/'packet/public/integrity_controls.py','--output',controls,*args],label='implementation-artifact-controls')
 result['implementation_artifact_controls']=json.loads((controls/'results.json').read_text())
 require(len(result['implementation_artifact_controls'])==11 and all(x['matched'] for x in result['implementation_artifact_controls']),'artifact controls')
 result['implementation_reverified']=v.verify(IMPL,*ANCHORS.values(),PROJECT)
 after=inv.snapshot()
 observations={'frontier/NEW-TEN-2026-10-14.md','frontier/campaigns/2026-10-14/discovery-analytic-r133-parent/formal-review-r1-dispatch.json'}
 require(before['complete_roots']==after['complete_roots'],'root set changed')
 require({k:v for k,v in before['entries'].items() if k not in observations}=={k:v for k,v in after['entries'].items() if k not in observations},'original stable snapshot changed during replay')
 result['originals_unchanged_during_replay']=True
 result['all_expected']=True
 (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'all_expected':True,'implementation_declarations':41,'review_declarations':len(names),'semantic_mutations':len(mutation_results),'artifact_controls':11}))
if __name__=='__main__':main()
