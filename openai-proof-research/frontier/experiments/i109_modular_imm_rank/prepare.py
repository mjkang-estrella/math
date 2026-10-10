"""One-time preparation; writes only I109-owned paths. Not the final verifier."""
import pathlib,json,hashlib,shutil,re
R=pathlib.Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i109_modular_imm_rank';X=R/'frontier/experiments/i109_modular_imm_rank'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
assert not (S/'immutable-references.json').exists()
refs=[]
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','frontier/iterations/iteration109-modular-imm-rank-task.json','frontier/iterations/iteration106-positive-characteristic-imm-task.json','frontier/iterations/i106-positive-characteristic-imm.md','frontier/experiments/i106-parent-verification.json']:
 p=R/rel;q=S/'snapshots'/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 refs.append({'path':rel,'sha256':sha(p),'snapshot':str(q.relative_to(R)),'drift_allowed':rel in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
old=R/'frontier/sources/i106_positive_characteristic_imm'
shutil.copyfile(old/'seal.json',S/'original-seal.json')
for rel in ['frontier/sources/i106_positive_characteristic_imm/seal.json','frontier/sources/i103_algebraic_complexity_discovery/seal.json']:
 refs.append({'path':rel,'sha256':sha(R/rel),'drift_allowed':False})
task=json.loads((S/'snapshots/frontier/iterations/iteration109-modular-imm-rank-task.json').read_text())
b=task['brief'];(S/'complete-launch-brief.txt').write_text(b);(S/'complete-additional-instructions.txt').write_text(task['additional_instructions'])
a,b=b.split('--- ORIGINAL I106 BRIEF ---',1); origbrief,b=b.split('--- ORIGINAL I106 REPORT ---',1); origreport,origparent=b.split('--- FINAL PARENT RESPONSE ---',1)
(S/'original-brief.txt').write_text(origbrief);(S/'original-report.txt').write_text(origreport);(S/'original-parent.txt').write_text(origparent)
assert origreport.strip()==(R/'frontier/iterations/i106-positive-characteristic-imm.md').read_text().strip()
assert json.loads(origparent)==json.loads((R/'frontier/experiments/i106-parent-verification.json').read_text())
dump(S/'immutable-references.json',refs)
dump(S/'preparation-events.json',[
 {'event':'Initial broad rg lookup and combined ledger reads truncated; no complete reading claimed for truncated output.'},
 {'event':'Guessed 05-path-sum.tex absent; located actual 05-paths.tex with rg --files --no-ignore; missing read not logged.'},
 {'event':'A later oversized ledger search truncated; complete relevant I106 integration read separately.'}])
# Reuse complete inherited mapping and exact old occurrence multisets in place, no corpus copy.
domain=json.loads((R/'frontier/sources/i103_algebraic_complexity_discovery/search-domain.json').read_text())
queries={'mechanisms':r'(?i)(Smith normal form|inclusion matr(?:ix|ices)|divided.power|contraction operator|homogeneous.{0,12}depth.{0,6}five|iterated matrix multiplication)'}
dump(S/'queries.json',queries); hits=[]
for d in domain:
 for ln,line in enumerate((R/d['local']).read_text(errors='replace').splitlines(),1):
  for name,expr in queries.items():
   for m in re.finditer(expr,line):hits.append({'query':name,'path':d['path'],'line':ln,'start':m.start(),'end':m.end(),'text':line})
(S/'lexical-hits.jsonl').write_text(''.join(json.dumps(h,ensure_ascii=False)+'\n' for h in hits))
dump(S/'search-summary.json',{'positions':len(domain),'manuscripts':749,'tree_entries':13223,'occurrences':len(hits),'convention':'UTF-8 errors=replace; str.splitlines(), 1-based; start/end zero-based Unicode codepoints','scope':'Lexical coverage only, not full semantic reading; inherited I106 full target/field/rank occurrence multisets replayed in place.'})
print({'snapshot_refs':len(refs),'original_positions':len(domain),'new_occurrences':len(hits)})
