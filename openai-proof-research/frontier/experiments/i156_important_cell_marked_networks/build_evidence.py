"""Prepare owned evidence metadata before sealing; never run after the seal."""
from pathlib import Path
import json, hashlib, re
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i156_important_cell_marked_networks'
OLD='frontier/sources/i151_spatial_dynamical_percolation_continuation'
def get(p): return json.loads((ROOT/p).read_text())
def sha(b): return hashlib.sha256(b).hexdigest()
def put(p,x): (ROOT/p).write_text(json.dumps(x,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
def bind(p):
 b=(ROOT/p).read_bytes();return {'path':p,'sha256':sha(b),'bytes':len(b)}
assert not (ROOT/S/'seal.json').exists()
progress=get(S+'/progress.json')
# These texts were read from the user's complete original and/or earlier bounded displays.
manual=[('frontier/sources/i151_spatial_dynamical_percolation_continuation/spatial-continuation.md','complete original supplied in task; bound unchanged local text'),
        (OLD+'/gps-operation-notes.md','complete earlier direct display'),
        (OLD+'/van-operation-notes.md','complete earlier direct display'),
        ('AGENTS.md','complete direct display'),
        ('sources/upstream.json','initial direct display'),
        ('sources/CONTENTS.md','initial direct display')]
for p,method in manual:
 if any(r['path']==p and r['start']==1 and r['end']==len((ROOT/p).read_text().splitlines()) for r in progress['read_passages']):continue
 b=(ROOT/p).read_bytes();ls=b.decode().splitlines()
 progress['read_passages'].append({'path':p,'start':1,'end':len(ls),'total_lines':len(ls),'sha256':sha(b),'passage_sha256':sha('\n'.join(ls).encode()),'ending':ls[-1],'displayed':True,'method':method})
progress['display_failures']=[
 {'scope':'initial rg listing','reason':'truncated discovery listing; no semantic coverage'},
 {'scope':'context chunk 4 groups 744-801','reason':'outer tool truncation','recovered':True},
 {'scope':'context group 1483 escaped receipt stdout','reason':'truncated long line','recovered':True},
 {'scope':'progress.json display after compaction','reason':'truncated metadata display; no new semantic claim'},
 {'scope':'GPS pivotal rg and historical reading-plan displays','reason':'truncated discovery/metadata outputs; operative passages separately read'},
 {'scope':'I151 parent requested lines 1-240','reason':'range assertion: actual total 154; no passage emitted','recovered':'complete 1-154 display'}]
ctx=get(OLD+'/context-reading-plan.json')
covered=set(progress['context_extra_read'])
for i in progress['context_chunks_read']:covered.update(ctx['chunks'][i])
lines=set()
for r in progress['read_passages']:lines.update((ROOT/r['path']).read_text().splitlines()[r['start']-1:r['end']])
reused=[]
for i,g in enumerate(ctx['groups']):
 p=g['representative'];line=(ROOT/p['path']).read_text().splitlines()[p['line']-1]
 if i not in covered and line in lines: covered.add(i);reused.append(i)
assert covered==set(range(3342)),sorted(set(range(3342))-covered)
progress['original_reading_complete']=True
progress['task_status']='AUDIT AND PARTIAL CONTINUATION RECORDED; full target unresolved'
progress['context_exact_reuse_groups']=reused
progress['context_plan_reference']=OLD+'/context-reading-plan.json'
progress['semantic_scope']='declared readings only; immutable validation does not certify comprehension'
put(S+'/progress.json',progress)
scope={}
for r in progress['read_passages']:scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
for r in ctx['files']:scope.setdefault(r['path'],set()).update(range(1,r['lines']+1))
coverage=[]
expressions={'arms':r'four[- ]arm|six[- ]arm|three[- ]arm|alpha4|A151-rem',
 'annotations':r'Palm|Mecke|membership|history|seam|forced|network|Boolean',
 'limits':r'quenched|replica|calibrat\w*|entourage|hereditar\w*|J1|Skorokhod',
 'historical':r'INCOMPLETE|FAIL|PASS|unresolved|PARK'}
occ={k:[] for k in expressions}
for p,ns in sorted(scope.items()):
 ls=(ROOT/p).read_text().splitlines();ranges=[]
 for n in sorted(ns):
  if not ranges or n>ranges[-1][1]+1:ranges.append([n,n])
  else:ranges[-1][1]=n
  for k,rx in expressions.items():
   for m in re.finditer(rx,ls[n-1],re.I):occ[k].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group()})
 coverage.append({'path':p,'sha256':sha((ROOT/p).read_bytes()),'ranges':ranges,'covered_lines':len(ns),'total_lines':len(ls),'complete':len(ns)==len(ls),'ending':ls[max(ns)-1]})
put(S+'/reading-coverage.json',{'files':coverage,'context_representations':39,'context_distinct_lines':3342,'context_line_occurrences':13094,'passages':len(progress['read_passages']),'scope':'I156 actual declarations; no inheritance of all I151 primary reading as I156 reading'})
put(S+'/lexical.json',{'expressions':expressions,'occurrences':occ,'counts':{k:len(v) for k,v in occ.items()},'convention':'Unicode splitlines, zero-based half-open character positions, case-insensitive re; duplicates at different positions retained'})
snap=[]
for p in ('README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'):
 q=S+'/snapshots/'+p.replace('/','__');(ROOT/q).parent.mkdir(exist_ok=True)
 if not (ROOT/q).exists():(ROOT/q).write_bytes((ROOT/p).read_bytes())
 snap.append({'live_path':p,'snapshot':q,**{k:v for k,v in bind(q).items() if k!='path'},'live_drift_allowed':True})
put(S+'/snapshots.json',snap)
flat={r['path']:r for r in get(OLD+'/immutable-flat.json')['files']}
se=get(OLD+'/seal.json')
for r in se['files']:flat[r['path']]=r
for p in (OLD+'/seal.json','frontier/experiments/i151-parent-verification.json','frontier/iterations/iteration151-spatial-dynamical-percolation-continuation-task.json'):
 flat[p]=bind(p)
for p in scope:
 if not p.startswith(S+'/'):flat[p]=bind(p)
assert not any(re.search(r'/(?:i|iteration)(154|155)[-_]',p) for p in flat)
put(S+'/immutable-flat.json',{'files':[flat[p] for p in sorted(flat)],'scope':'one flat deduplicated union; no ancestor execution and no corpus copy'})
put(S+'/disposition.json',{'accepted_count':8,'remaining_count':2,'nomination':None,'original_I149_task':'INCOMPLETE','original_I149_evidence':'PASS','original_I122':'literal general-Lambda FAIL','original_I125':'literal inventory FAIL; distinct ordering-only adapter PASS','original_I151_B':'PASS without repairs','original_I151_exact_inclusion':'FAIL','original_I151_overlap_extraction':'unresolved as exhibited; separate I156 extension','target':'PARK/unresolved','A151_rem_omitted_mass_modulus':'not proved','paid_separation_failure_mass':'C_K alpha4(delta,1)^-1 u, e first','task_scope':'original audit plus partial continuation; no full marked-network theorem'})
print(json.dumps({'flat_files':len(flat),'passages':len(progress['read_passages']),'context_groups':len(covered),'coverage_files':len(coverage),'lexical_occurrences':sum(map(len,occ.values()))}))
