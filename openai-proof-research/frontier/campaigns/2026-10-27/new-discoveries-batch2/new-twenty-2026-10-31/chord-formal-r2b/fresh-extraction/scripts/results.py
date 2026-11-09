from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent.parent
mods=(R/'modules.txt').read_text().splitlines()
inherited=(R/'inherited-modules.txt').read_text().splitlines()
modules=[]
for m in mods:
 p=R/'src'/f'{m}.lean'
 modules.append({'module':m,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines()),'inherited':m in inherited,'fresh_replay':(R/'fresh-extraction'/'build'/f'{m}.ok').exists()})
counts={k:{'declarations':0,**{x:0 for x in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern','unapproved_transitive_axioms']}} for k in ['local','upstream']}
audit=R/'fresh-extraction'/'audit.jsonl'
if audit.exists():
 for line in audit.open():
  row=json.loads(line);k='local' if row['local'] else 'upstream';counts[k]['declarations']+=1
  for flag in ['unsafe','partial','axiom','unsafe_rec','implemented_by','extern']:counts[k][flag]+=row[flag]
  counts[k]['unapproved_transitive_axioms']+=any(a not in ['propext','Classical.choice','Quot.sound'] for a in row['axioms'])
same=all((R/'src'/f'{m}.lean').read_bytes()==(R/'frozen'/f'{m}.lean').read_bytes()==(R/'fresh-extraction'/'src'/f'{m}.lean').read_bytes() for m in inherited)
peaks=[]
for root in [R/'logs',R/'fresh-extraction'/'logs']:
 for p in root.glob('*.log'):
  for l in p.read_text(errors='replace').splitlines():
   if l.startswith('PEAK_RSS_KIB='):peaks.append(int(l.split('=')[1]))
res={'mathdb_id':329080,'round':'2B','status':'PARTIAL_NOT_ACCEPTED','self_accepted':False,'root_decides':True,'credit':0,
'frozen_archive_sha256':'03971d4610581095feddea8040bd178f017d459794ac3e2374e73402d93ccbab','frozen_33_byte_identical':same,
'closed_Props':['FiveChordLemma','FourChordEnumeration'],
'partial_targets':{'TriangleRigidity':'n=3 proved; n>=5 remains','RepresentativeExistence':'base n=3 and induction assembly only; general step unproved'},
'remaining_combinatorial_Props':['RepresentativeExistence','BipartitePlanarity','TriangleReduction','TriangleRigidity'],
'model_Props_not_claimed':['DartBridge','OrbitCounterCorrect','FacePermutationCorrect','EulerRealization','Deletion','Heredity'],
'conditional_hypotheses':{'conj34_intended':['RepresentativeExistence','Heredity','TriangleReduction','TriangleRigidity'],'conj34_intended_reduced':['RepresentativeStep','Heredity','TriangleReduction','TriangleRigidityLarge'],'conj34_n4':[]},
'auxiliary_unconditional':['triangle_three','triangleRigidity_three','range_three_complete','exactly_one_three','negative_unique_four'],
'audit':counts,'audit_inventory':sum(v['declarations'] for v in counts.values()),'modules':modules,
'validation':{'fresh_extracted_serial_rebuild':all(m['fresh_replay'] for m in modules),'per_module_leanchecker':all(m['fresh_replay'] for m in modules),'peak_sampled_RSS_KiB':max(peaks,default=0),'resource_caps':{'rss_GiB':6,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'lean_M':3500}},
'lean':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612'}
(R/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ['modules']},indent=1))
