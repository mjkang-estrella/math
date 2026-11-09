#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT; see packet/public/LICENSE-CODE.txt.
"""Portable routing for unchanged reviewed code; writes only to a NEW output tree.
First authenticate the complete archive/extraction with externally anchored verify.py.
Output must be outside the immutable release root. No installer or network calls.
"""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
PDF_SHA='c4e15a10f86623abe2919c36f4863971cea611d705dd3bcbc9684cff260a8647'
def req(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 data={}
 for d,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(d)/n;st=p.lstat();req(not p.is_symlink(),'symlink input '+str(p))
   v={'mode':stat.S_IMODE(st.st_mode),'kind':'directory' if p.is_dir() else 'file'}
   if not p.is_dir():req(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular input');v.update(sha256=sha(p),bytes=st.st_size)
   data[p.relative_to(root).as_posix()]=v
 return data
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('mode',choices=['exact','formal','pdf','all']);ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--lean',type=Path);ap.add_argument('--cache',type=Path,help='explicit trusted Lean .lake/packages directory')
 ap.add_argument('--tectonic',type=Path);ap.add_argument('--tex-cache',type=Path,help='explicit populated XDG cache, copied before use')
 ap.add_argument('--python-path',type=Path,help='explicit installed SymPy1.14.0/mpmath1.3.0 package directory; otherwise current Python environment')
 a=ap.parse_args();out=a.output.absolute();req(not out.exists() and not out.is_symlink(),'fresh output required')
 for p in out.parents:req(not p.is_symlink(),'output ancestor symlink')
 req(not out.is_relative_to(ROOT) and not ROOT.is_relative_to(out),'output overlaps immutable release')
 for name in ['lean','cache','tectonic','tex_cache','python_path']:
  p=getattr(a,name)
  if p is not None:
   p=p.resolve();setattr(a,name,p);req(not p.is_relative_to(out) and not out.is_relative_to(p),'output overlaps dependency '+name)
 if a.mode in ['formal','all']:req(a.lean and a.cache,'supply --lean and --cache')
 if a.mode in ['pdf','all']:req(a.tectonic and a.tex_cache,'supply --tectonic and --tex-cache')
 before=inventory(ROOT);out.mkdir(parents=True)
 for d in ['tmp','config','data','cache','home','logs']:(out/d).mkdir()
 env=os.environ.copy();env.update(PYTHONDONTWRITEBYTECODE='1',TMPDIR=str(out/'tmp'),TMP=str(out/'tmp'),TEMP=str(out/'tmp'),XDG_CACHE_HOME=str(out/'cache'),XDG_CONFIG_HOME=str(out/'config'),XDG_DATA_HOME=str(out/'data'),SOURCE_DATE_EPOCH='1792454400')
 if a.python_path:env['PYTHONPATH']=str(a.python_path)
 else:env.pop('PYTHONPATH',None)
 result={'schema':'T088P133-portable-reproduction-v1','mode':a.mode,'status':'RUNNING','commands':[],'full_theorem_formalized':False,'gate_assigned':False,'trust':'Clean archive extraction with explicit trusted tools; no OS isolation, complete supply-chain authentication or dependency-source rebuild.'}
 def run(argv,cwd,label,extra=None):
  e=env.copy();e.update(extra or {});c=subprocess.run([str(x) for x in argv],cwd=cwd,env=e,text=True,capture_output=True)
  path=out/'logs'/ (label+'.log');path.write_text(c.stdout+c.stderr)
  result['commands'].append({'argv':[str(x) for x in argv],'cwd':str(cwd),'exit':c.returncode,'log':str(path.relative_to(out)),'sha256':sha(path)})
  req(c.returncode==0,'failed '+label+'; see '+str(path));return c.stdout
 try:
  # Compatible copied relative layout, never a borrowed source directory.
  public=out/'packet/public';shutil.copytree(ROOT/'packet/public',public)
  for p in public.rglob('*'):
   if p.is_file():p.chmod(0o644)
  if a.mode in ['exact','all','pdf']:
   run([sys.executable,'-B',public/'support/reproduce.py',out/'exact'],out,'exact')
   req((out/'exact/witness-tables.tex').read_bytes()==(public/'witness-tables.tex').read_bytes(),'all printed table bytes')
   result['exact']=json.loads((out/'exact/exact-results.json').read_text())
   result['table_bytes_identical']=True
  if a.mode in ['exact','all']:
   versions=run([sys.executable,'-B','-c','import sympy,mpmath; assert sympy.__version__=="1.14.0" and mpmath.__version__=="1.3.0"; print(sympy.__version__,mpmath.__version__)'],out,'symbolic-versions')
   # Original independent script expects O/code and O/work/extracted/packet/public.
   independent=out/'independent';(independent/'code').mkdir(parents=True);(independent/'evidence').mkdir()
   shutil.copytree(public,independent/'work/extracted/packet/public')
   shutil.copy2(public/'support/independent_exact.py',independent/'code/independent_exact.py')
   run([sys.executable,'-B',independent/'code/independent_exact.py'],out,'independent-exact')
   result['independent_exact']=json.loads((independent/'evidence/independent-exact.json').read_text())
  if a.mode in ['formal','all']:
   run([sys.executable,'-B',public/'support/formal_reproduce.py','--lean',a.lean,'--cache',a.cache,'--output',out/'build/work/formal'],out,'formal')
   result['formal']=json.loads((out/'build/work/formal/receipt.json').read_text())
  if a.mode in ['pdf','all']:
   pins=json.loads((ROOT/'tool-inputs.json').read_text());req(sha(a.tectonic)==pins['tectonic_sha256'],'Tectonic binary SHA')
   before_cache=inventory(a.tex_cache);expected=pins['tex_cache_files'];actual={p:v for p,v in before_cache.items() if v['kind']=='file'}
   req(set(actual)==set(expected),'declared TeX cache file set')
   for p,v in expected.items():req(actual[p]['bytes']==v['bytes'] and actual[p]['sha256']==v['sha256'],'TeX cache byte mismatch '+p)
   shutil.copytree(a.tex_cache,out/'build/cache');tex=out/'build/tex';tex.mkdir()
   extra={'XDG_CACHE_HOME':str(out/'build/cache')}
   version=run([a.tectonic,'--version'],out,'tectonic-version',extra)
   req('0.17.0' in version,'Tectonic version')
   run([a.tectonic,'--only-cached','--untrusted','--keep-logs','--keep-intermediates','--reruns','2','--outdir',tex,'main.tex'],public,'tex-build',extra)
   run([sys.executable,'-B',public/'support/qa.py',out],out,'tex-qa')
   result['pdf']={'sha256':sha(tex/'main.pdf'),'matches_reviewed_pdf':sha(tex/'main.pdf')==PDF_SHA,'source_date_epoch':1792454400,'engine_sha256':sha(a.tectonic),'only_cached':True,'declared_cache_files':len(expected),'borrowed_cache_unchanged':inventory(a.tex_cache)==before_cache,'qa':json.loads((out/'build/log-qa.json').read_text())}
   (out/'renders').mkdir()
   run(['pdftoppm','-r','120','-png',tex/'main.pdf',out/'renders/page'],out,'pdf-render')
   run(['pdftotext','-layout',tex/'main.pdf',out/'main.txt'],out,'pdf-text')
   info=run(['pdfinfo',tex/'main.pdf'],out,'pdfinfo');result['pdf']['pdfinfo']=info
   result['pdf']['renders']={p.name:sha(p) for p in sorted((out/'renders').glob('*.png'))}
   req(result['pdf']['borrowed_cache_unchanged'],'borrowed cache changed')
   req(result['pdf']['matches_reviewed_pdf'],'PDF differs; do not replace reviewed paper')
  result['status']='REPRODUCED'
 finally:
  result['immutable_release_unchanged']=inventory(ROOT)==before
  (out/'receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
  req(result['immutable_release_unchanged'],'immutable release changed')
 print(json.dumps({'status':result['status'],'mode':a.mode,'immutable_release_unchanged':True,'receipt':str(out/'receipt.json'),'gate_assigned':False}))
if __name__=='__main__':main()
