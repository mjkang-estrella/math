"""Preparation only, never called by the offline verifier; refuses to change a sealed round."""
import json,hashlib,re
from pathlib import Path
S=Path('frontier/sources/i146_effective_boundary_exclusion')
assert not (S/'seal.json').exists()
def put(p,v):Path(p).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def ident(p):
 b=Path(p).read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
reads=[json.loads(l) for l in (S/'read-log.jsonl').read_text().splitlines()]
reads=[r for r in reads if not ((r['path'].endswith('/pqs.txt') and (r['start'],r['end'])==(429,889)) or (r['path'].endswith('/li-souplet.txt') and (r['start'],r['end'])==(1,295)))]
for r in reads:
 if '/corpus/preprints/' in r['path']:r['pinned_url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/'+r['path'].split('/corpus/preprints/',1)[1]
put(S/'read-manifest.json',{'convention':'Python splitlines; LF joined without appended LF for passage hashes; ranges inclusive','passages':reads,'discarded_displays':'The two truncated combined source displays are retained in raw read-log but excluded from semantic passage manifest; complete replacement reads cover them.'})
ctx=json.loads((S/'context-manifest.json').read_text());put(S/'context-reading.json',{'all_decoded_fields':True,'records':ctx,'total_lines':sum(r['lines'] for r in ctx),'gate':'All nine decoded records read before mathematical original audit; no status/title-only substitution.'})
originals=json.loads((S/'originals.json').read_text())
if len(originals)>2:
 put(S/'self-task-snapshot-note.json',{'snapshot':originals[2]['snapshot'],'sha256':originals[2]['sha256'],'note':'Snapshot of this round input only; active orchestration record is not an immutable dependency or drift exception.'})
 put(S/'originals.json',originals[:2])
verdict={'original_I143_paid_assertions':'PASS without repairs at stated scopes','new_original_FAIL':[],'unresolved_original_paid_assertions':[],'original_unpaid':['effective K0','reflected radial pressure'],'inherited_I125_literal':'FAIL canonical inventory, unchanged','inherited_I125_ordering_only':'distinct PASS, not rerun','inherited_I122_general_Lambda':'FAIL unchanged','parent_review':'selective, not full original-proof pass'}
put(S/'original-audit-verdicts.json',verdict)
put(S/'research-disposition.json',{'accepted_count':8,'remaining_count':2,'nomination':None,'qualitative_target_L':'preserved technical bound','effective_boundary_exclusion':'PARK','reflected_radial_pressure':'PARK','new_paid':['A146.1-A146.6','Holder interval retention','B146.1-B146.2','C146.1-C146.3'],'other_parked_branches':'unchanged'})
expr={'boundary':r'half[- ]?space|half[- ]?ball|boundary|Dirichlet','pressure':r'pressure|virial|Pohozaev|interval|localization','effectiveness':r'compactness|effective|quantitative|constant|normaliz','kernel':r'Green|Newton|harmonic|reflect|moment'}
occ={k:[] for k in expr};scope={}
for r in reads:scope.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
for p,lines in sorted(scope.items()):
 ls=Path(p).read_text().splitlines()
 for n in sorted(lines):
  for k,e in expr.items():
   for m in re.finditer(e,ls[n-1],re.I):occ[k].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
put(S/'focused-lexical.json',{'expressions':expr,'occurrences':occ,'counts':{k:len(v) for k,v in occ.items()},'scope':'exact multiset over union of actually read passage lines, not semantic proof coverage'})
domain=json.loads(Path('frontier/sources/i113_online_optimization_discovery/search-domain.json').read_text());selected=[d for d in domain if d['local'] in scope or d['original_local'] in scope];put(S/'selected-inventory.json',selected)
flat=json.loads((S/'immutable-flat.json').read_text())['files'];mapping={r['path']:r for r in flat}
for p in scope:
 if not p.startswith(str(S)+'/') and p not in mapping:mapping[p]=ident(p)
for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/experiments/i131_soft_summary_stability/extract_html.py']:
 if p not in mapping:mapping[p]=ident(p)
put(S/'immutable-flat.json',{'files':[mapping[p] for p in sorted(mapping)]})
print(json.dumps({'passages':len(reads),'context_lines':sum(r['lines'] for r in ctx),'flat':len(mapping),'selected_originals':len(selected),'lexical':{k:len(v) for k,v in occ.items()}},indent=2))
