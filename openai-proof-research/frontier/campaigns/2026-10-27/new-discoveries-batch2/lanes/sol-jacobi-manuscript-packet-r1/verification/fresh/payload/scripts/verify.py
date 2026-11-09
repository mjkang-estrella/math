#!/usr/bin/env python3
"""Source-only sequential whole-certificate audit. Writes only beneath fresh destination."""
import collections,hashlib,json,re,resource,shutil,subprocess,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from pins import check,sha
CAP=512*1024*1024; ALLOW={'propext','Classical.choice','Quot.sound'}
def main():
 base=Path(sys.argv[1]).resolve(); dest=Path(sys.argv[2]).resolve(); assert not dest.exists()
 dest.mkdir(parents=True); src=dest/'formal'; shutil.copytree(base/'formal',src)
 config=json.loads((base/'component.json').read_text()); modules=config['mathematical_modules']; assert len(modules)==len(set(modules))==35
 assert not any(p.suffix in {'.olean','.ilean','.ir','.o','.so'} for p in src.rglob('*'))
 initial={p.name:sha(p) for p in src.iterdir() if p.is_file()}
 pins_before=check(base); (dest/'pins-before.json').write_text(json.dumps(pins_before,indent=2)+'\n')
 for n in modules:
  assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac|implemented_by)\b',(src/(n+'.lean')).read_text()),n
 steps=[]
 def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(CAP,CAP))
 def run(n,mathematical=False):
  print('BUILD '+n,flush=True)
  with (src/(n+'.driver.log')).open('wb') as out:
   p=subprocess.run([sys.executable,'guard.py',n+'.lean.log','-o',n+'.olean',n+'.lean'],cwd=src,stdout=out,stderr=subprocess.STDOUT,preexec_fn=limit)
  assert p.returncode==0,(n,str(src/(n+'.lean.log')))
  rec=json.loads((src/(n+'.lean.log.json')).read_text()); assert rec['exit_code']==0 and not rec['guard_killed'] and rec['sampled_peak_rss_kib']<=3145728
  if mathematical:assert (src/(n+'.lean.log')).stat().st_size==0,n
  steps.append({'module':n,**rec})
 for n in modules:run(n,True)
 run('WholeInventory')
 inv=(src/'WholeInventory.lean.log').read_text(); names=re.findall(r'^DECL (\S+)$',inv,re.M); origins=dict(re.findall(r'^ORIGIN (\S+) (\S+)$',inv,re.M)); unsafe=dict(re.findall(r'^UNSAFE (\S+) (true|false)$',inv,re.M))
 assert len(names)==len(set(names)); assert set(names)==set(origins)==set(unsafe); assert set(origins.values())==set(modules); assert set(unsafe.values())=={'false'}
 declarations=[]
 audit='WholeAudit'
 template=(base/'formal/WholeInventory.lean').read_text().replace('"#whole_inventory"','"#whole_audit"').replace('#whole_inventory\n','#whole_audit\n')
 template=template.replace('set_option pp.privateNames true','set_option pp.privateNames true\nset_option linter.auxLemma false')
 template=template.replace('        if info.isUnsafe then throwError m!"Unsafe declaration: {name}"','        if info.isUnsafe then throwError m!"Unsafe declaration: {name}"\n        elabCommand (← `(#check $(mkIdent name)))\n        elabCommand (← `(#print axioms $(mkIdent name)))')
 (src/(audit+'.lean')).write_text(template)
 run(audit)
 report=(src/(audit+'.lean.log')).read_text()
 ax={n:re.findall(r'[\w.]+',a) for n,a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",report,re.M)}
 empty=re.findall(r"^'([^']+)' does not depend on any axioms$",report,re.M)
 assert set(names)==set(ax)|set(empty),'axiom coverage'
 assert all(set(a)<=ALLOW for a in ax.values())
 for n in sorted(names):
  assert re.search(r'^'+re.escape(n)+r'(?:\s|\.|\{|\(|:)',report,re.M),(n,'missing actual #check')
  declarations.append({'name':n,'origin':origins[n],'isUnsafe':False,'axioms':ax.get(n,[]),'actual_type_and_axiom_report':'formal/WholeAudit.lean.log'})
 run('SourceClaimInterfaces')
 run('ExpandedEndpoint')
 for n,h in initial.items():assert sha(src/n)==h,n
 pins_after=check(base);assert pins_before==pins_after
 (dest/'pins-after.json').write_text(json.dumps(pins_after,indent=2)+'\n')
 (dest/'declarations.json').write_text(json.dumps(declarations,indent=2)+'\n')
 diagnostics=sum(p.stat().st_size for p in dest.rglob('*.log'));assert diagnostics<=CAP
 receipt={'status':'PASS','mathematical_module_count':35,'mathematical_logs_all_empty':True,'full_generated_origin_declaration_count':len(names),'manually_selected_declarations':0,'origin_counts':dict(sorted(collections.Counter(origins.values()).items())),'all_35_origins_covered':True,'actual_check_and_print_axioms_for_every_declaration':True,'all_isUnsafe_false':True,'allowed_axioms':sorted(ALLOW),'endpoint':config['endpoint'],'source_hashes_unchanged':initial,'pins_before_after_equal':True,'initial_local_prebuilt_artifacts':[],'flags':['-j1','-M4096','-DwarningAsError=true','-DautoImplicit=false'],'sampled_process_tree_rss_ceiling_kib':3145728,'peak_sampled_process_tree_rss_kib':max(s['sampled_peak_rss_kib'] for s in steps),'diagnostics_cap_bytes':CAP,'diagnostics_bytes':diagnostics,'address_space_cap':None,'steps':steps}
 (dest/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PASS '+str(len(names))+' complete module-origin declarations',flush=True)
if __name__=='__main__':main()
