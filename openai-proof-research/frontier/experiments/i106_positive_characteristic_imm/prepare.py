import pathlib,json,hashlib,shutil,re
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i106_positive_characteristic_imm'; OLD=R/'frontier/sources/i103_algebraic_complexity_discovery'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
assert sha(OLD/'seal.json')=='b3eaa8ec05a4bb443476b61d2af487ee73fb2393b992fef3ccfb572a8b59949f'
files=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','frontier/iterations/iteration103-algebraic-complexity-discovery-task.json','frontier/iterations/i103-algebraic-complexity-discovery.md','frontier/experiments/i103-parent-verification.json','frontier/iterations/iteration106-positive-characteristic-imm-task.json']
refs=[]
for f in files:
 p=R/f; dest=S/'snapshots'/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);refs.append({'path':f,'sha256':sha(p),'snapshot':str(dest.relative_to(R)),'drift_allowed':f in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']})
for f in ['seal.json','search-domain.json','selected-inventory.json','source-contracts.json','immutable-references.json','read-manifest.jsonl','queries.json','lexical-hits.jsonl']:
 p=OLD/f;refs.append({'path':str(p.relative_to(R)),'sha256':sha(p),'drift_allowed':False})
save(S/'immutable-references.json',refs)
brief=json.loads((R/files[-1]).read_text())['brief']
for start,end,name in [('FULL ORIGINAL I103 BRIEF:','FULL ORIGINAL I103 REPORT:','original-brief.txt'),('FULL ORIGINAL I103 REPORT:','FINALIZED PARENT RESPONSE / EVIDENCE RECORD:','original-report.txt')]:
 if start in brief and end in brief:(S/name).write_text(brief.split(start,1)[1].split(end,1)[0].strip()+'\n')
if 'FINALIZED PARENT RESPONSE / EVIDENCE RECORD:' in brief:
 (S/'original-parent.json').write_text(brief.split('FINALIZED PARENT RESPONSE / EVIDENCE RECORD:',1)[1].strip()+'\n')
shutil.copyfile(OLD/'seal.json',S/'original-seal.json')
save(S/'preparation-events.json',[{'event':'Initial shell lookup used parent cwd; ls failed; no writes'},{'event':'Two oversized metadata/ledger console reads truncated; not treated as complete semantic reads'}])
# Reuse full mapping; record exact occurrence multiset for new screen.
queries={'imm':r'(?i)iterated.matrix.multiplication|IMM|depth.five|depth.5','characteristic':r'(?i)positive.characteristic|every.field|arbitrary.field|finite.field','rank':r'(?i)divided.power|Hasse.derivative|unimodular|Smith.normal|shifted.partial'}
save(S/'queries.json',queries)
hits=[];domain=json.loads((OLD/'search-domain.json').read_text())
for rec in domain:
 text=(R/rec['local']).read_text(errors='replace')
 for ln,line in enumerate(text.splitlines(),1):
  for key,expr in queries.items():
   for match in re.finditer(expr,line):hits.append({'query':key,'path':rec['path'],'line':ln,'start':match.start(),'end':match.end(),'text':line})
with (S/'lexical-hits.jsonl').open('w') as f:
 for hit in hits:f.write(json.dumps(hit,ensure_ascii=False)+'\n')
save(S/'search-summary.json',{'positions':len(domain),'manuscripts':len({x['path'].split('/')[1] for x in domain}),'counts':{q:sum(h['query']==q for h in hits) for q in queries},'scope':'Exact lexical occurrences only; no full semantic audit'})
print(json.loads((S/'search-summary.json').read_text()))
