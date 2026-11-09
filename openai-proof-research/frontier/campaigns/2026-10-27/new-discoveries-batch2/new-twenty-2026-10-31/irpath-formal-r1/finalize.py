from pathlib import Path
import re,json,hashlib
root=Path('.')
mods=Path('module-order.txt').read_text().split()
for m in mods:
 assert Path(f'final-extraction/logs/{m}.replayed').exists(),m
 assert Path(f'final-extraction/{m}.lean').read_bytes()==Path(f'{m}.lean').read_bytes()
assert Path('final-extraction/logs/Audit.compile.log').exists()
audit=Path('final-extraction/logs/Audit.compile.log').read_text()
assert "'IR350452.conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]" in audit
assert "'IR350452.nonvacuity' depends on axioms: [propext, Classical.choice, Quot.sound]" in audit
# Strip nested Lean comments and quoted strings before token scanning.
def lean_tokens(s):
 i=0; out=[]; depth=0
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':depth+=1;i+=2
   elif s[i:i+2]=='-/':depth-=1;i+=2
   else:i+=1
  elif s[i:i+2]=='/-':depth=1;i+=2
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
forbidden=r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b|_unsafe_rec'
scan=[]
for m in mods:
 s=lean_tokens(Path(m+'.lean').read_text())
 hits=re.findall(forbidden,s)
 assert not hits,(m,hits)
 scan.append({'module':m,'forbidden_tokens':[]})
Path('logs/source-scan.json').write_text(json.dumps(scan,indent=2)+'\n')
certificate=json.loads(Path('../expanded-corpus-r209/outputs/certificate-350452.json').read_text())
res={
 'status':'formalization_complete_for_root_review','self_accepted':False,
 'endpoint':'IR350452.conjecture_false : ¬ IR350452.Conjecture',
 'residual_hypotheses':[], 'witness_vertices':9,'witness_edges':20,'IR':3,'IR_sets':9,
 'isomorphism':'IR350452.pathIso : SimpleGraph.pathGraph 9 ≃g IR350452.IRGraph IR350452.G9',
 'nonvacuity':'IR350452.nonvacuity : IR350452.IsIRGraph (SimpleGraph.pathGraph 2)',
 'axioms':['propext','Classical.choice','Quot.sound'],
 'lean_version':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'strict_fresh_extraction_replay':{'directory':'final-extraction','all_modules_compiled':True,'all_modules_leanchecked':True,'modules':mods,'warningAsError':True},
 'metadata_audit':{'log':'final-extraction/logs/Audit.compile.log','all_local_module_declarations':True,'passed':True},
 'source_scan':{'log':'logs/source-scan.json','passed':True},
 'source_zip_sha256':hashlib.sha256(Path('source.zip').read_bytes()).hexdigest(),
 'limits':{'memory_lean_MB':3500,'RSS_GiB':6,'CPU_seconds':120,'wall_seconds':140,'CPUs':[0,1],'MALLOC_ARENA_MAX':2},
 'limitations':['No claim that the cycle half is false on its own.','No independent acceptance or novelty adjudication in this lane.'],
 'development_failures':['Broad Mathlib import exceeded memory limit; narrowed imports.','Monolithic finite decision exceeded memory; split into list completeness and checks.','Routine elaboration errors repaired before final-extraction replay.'],
 'network_used':False,'git_used':False,'child_agents_used':False
}
Path('results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
