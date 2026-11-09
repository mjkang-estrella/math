from pathlib import Path
import hashlib,json,zipfile
L=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((L/'frozen-before.json').read_text())
after={n:sha(L/'src'/n) for n in frozen}
assert frozen==after
for n,h in frozen.items():assert sha(L.parent/'ulas-formal-r4/src'/n)==h
(L/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
mods={p.stem:dict(sha256=sha(p),lines=len(p.read_text().splitlines()),frozen=p.name in frozen) for p in sorted((L/'src').glob('*.lean'))}
for p in (L/'fresh-replay/src').glob('*.lean'):assert sha(p)==mods[p.stem]['sha256']
audit=json.loads((L/'fresh-replay/logs/audit-summary.json').read_text())
result=dict(lane='ulas-formal-r5b',mathdb_id=342364,status='ODD_PART_COMPLETE_NOT_ACCEPTANCE',self_accepted=False,
 frozen_input_sha256='8dd3e493824cc44263a25e243ae7eddea13cceaddc5597b6699cdc30255deb46',frozen_modules_identical=True,
 closed_props=['OddOneBound','OddThreeBound','OddOneEquality','OddThreeEquality','FifteenBound'],
 remaining_props=['EvenFormula'],remaining_odd_props=[],even_lane_work_performed=False,
 endpoints={'Ulas.Round5Odd.odd_theorem':'unconditional','Ulas.Round5Odd.mathdb_342364':'unconditional',
 'Ulas.Round5Odd.full_theorem':'conditional only on EvenFormula','Ulas.Round5Odd.conj61_some':'conditional only on EvenFormula'},
 modules=mods,audit=audit,validation={'fresh_extracted_strict_rebuild':True,'leanchecker_all_modules':True,
 'negative_controls_rejected':6,'regression5_checks':6400,'background_jobs_left':False},
 discipline={'child_agents':False,'git':False,'network':False,'external_messages':False,'browser_tabs':False})
(L/'results.json').write_text(json.dumps(result,indent=2)+'\n')
with zipfile.ZipFile(L/'ulas-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for d in ['src','scripts']:
  for p in sorted((L/d).glob('*')):
   if p.is_file():z.write(p,str(p.relative_to(L)))
 for n in ['TASK.txt','SUMMARY.md','REMAINING.md','NEXT-ROUND.md','PROOF.md','REPRODUCE.md','STATEMENT-CORRESPONDENCE.md','results.json','frozen-before.json','frozen-after.json','input-reading.json']:
  z.write(L/n,n)
(L/'ulas-source.zip.sha256').write_text(sha(L/'ulas-source.zip')+'  ulas-source.zip\n')
print('LOCAL',audit['LOCAL'])
print('closure',audit['endpoint_import_closure'])
print('modules',len(mods),'archive',sha(L/'ulas-source.zip'))
