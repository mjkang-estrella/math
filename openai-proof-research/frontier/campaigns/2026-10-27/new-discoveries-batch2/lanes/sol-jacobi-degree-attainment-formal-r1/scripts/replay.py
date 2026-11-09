#!/usr/bin/env python3
"""Extract a source-only component and strictly rebuild it sequentially."""
import hashlib,json,re,resource,shutil,subprocess,sys,zipfile
from pathlib import Path

CAP=512*1024*1024
ALLOW={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def revision(m):
 g=m/'.git'
 if g.is_file():g=(m/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  r=h[5:]; f=g/r
  h=f.read_text().strip() if f.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+r))
 return h

def main():
 packet=Path(sys.argv[1]).resolve(); dest=Path(sys.argv[2]).resolve()
 assert not dest.exists(), 'fresh extraction destination must not exist'
 dest.mkdir(parents=True)
 with zipfile.ZipFile(packet) as z:
  assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
  assert not any(n.endswith(('.olean','.ilean','.ir','.o','.so')) for n in z.namelist())
  z.extractall(dest)
 initial=list(dest.rglob('*.olean'))
 assert not initial
 src=dest/'formal'
 manifest=json.loads((dest/'manifest.json').read_text())
 for n,h in manifest.items():assert sha(dest/n)==h,n
 pins=json.loads((dest/'pins.json').read_text())
 assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
 assert revision(Path(pins['mathlib']))==pins['mathlib_revision']
 config=json.loads((dest/'component.json').read_text())
 for n in config['proof_modules']:
  s=(src/(n+'.lean')).read_text()
  assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac|implemented_by)\b',s),n
 steps=[]
 def limit_diagnostics():resource.setrlimit(resource.RLIMIT_FSIZE,(CAP,CAP))
 for n in config['build_order']:
  print('BUILD '+n,flush=True)
  log=src/(n+'.driver.log')
  with log.open('wb') as out:
   result=subprocess.run([sys.executable,'guard.py',n+'.lean.log','-o',n+'.olean',n+'.lean'],cwd=src,stdout=out,stderr=subprocess.STDOUT,preexec_fn=limit_diagnostics)
  assert result.returncode==0,log
  receipt=json.loads((src/(n+'.lean.log.json')).read_text())
  assert receipt['exit_code']==0 and not receipt['guard_killed']
  assert receipt['sampled_peak_rss_kib']<=3*1024*1024
  steps.append(receipt)
  if n not in config['audit_modules']:assert not (src/(n+'.lean.log')).read_bytes(),n
 inv=(src/'DegreeAttainmentInventory.lean.log').read_text()
 names=re.findall(r'^ATTAINMENT_DECL (\S+)$',inv,re.M)
 origins=dict(re.findall(r'^ATTAINMENT_MODULE (\S+) (\S+)$',inv,re.M))
 safety=dict(re.findall(r'^ATTAINMENT_SAFETY (\S+) (true|false)$',inv,re.M))
 assert set(names)==set(origins)==set(safety)
 assert set(origins.values())==set(config['proof_modules'])
 assert all(v=='false' for v in safety.values())
 audit=(src/'DegreeAttainmentAudit.lean.log').read_text()
 ax={n:re.findall(r'[\w.]+',x) for n,x in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",audit,re.M)}
 empty=re.findall(r"^'([^']+)' does not depend on any axioms$",audit,re.M)
 assert set(names)==set(ax)|set(empty)
 assert all(set(a)<=ALLOW for a in ax.values())
 for n,h in manifest.items():assert sha(dest/n)==h,n
 diagnostics=sum(p.stat().st_size for p in dest.rglob('*.log'))
 assert diagnostics<=CAP
 receipt={'status':'PASS','packet_sha256':sha(packet),'initial_prebuilt_artifacts':[],
  'source_manifest_verified_before_and_after':True,'pins':pins,
  'sequential':True,'flags':['-j1','-M4096','-DwarningAsError=true','-DautoImplicit=false'],
  'rss_guard_kib':3*1024*1024,'peak_sampled_process_tree_rss_kib':max(x['sampled_peak_rss_kib'] for x in steps),
  'diagnostics_cap_bytes':CAP,'diagnostics_bytes':diagnostics,
  'all_mathematical_declarations_have_actual_check_print_axioms':True,
  'all_origin_declarations_isUnsafe_false':True,'allowed_axioms':sorted(ALLOW),
  'declarations':[{ 'name':n,'module':origins[n],'isUnsafe':False,'axioms':ax.get(n,[])} for n in sorted(names)],
  'build_steps':steps}
 (dest/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print('PASS: extracted source-only replay, exhaustive origin/type/axiom/safety audit.',flush=True)
if __name__=='__main__':main()
