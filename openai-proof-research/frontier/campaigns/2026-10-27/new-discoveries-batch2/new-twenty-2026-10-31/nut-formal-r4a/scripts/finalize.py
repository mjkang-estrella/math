from pathlib import Path
import json,hashlib,re,zipfile,collections
r=Path(__file__).resolve().parents[1]
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((r/'inputs-before.json').read_text())
after={p:hashfile(Path(p)) for p in before}
assert before==after,'Read-only input changed'
(r/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
for p,v in before.items():
 src=Path(p); copy=r/'inputs'/src.relative_to(r.parent)
 assert hashfile(copy)==v
for p in (r/'inputs/nut-formal-r3a/formal').glob('*.lean'):
 assert p.read_bytes()==(r/'formal'/p.name).read_bytes()
assert (r/'formal/FiniteGrammar.lean').read_bytes()==(r/'inputs/nut-formal-r2/formal/FiniteGrammar.lean').read_bytes()
manifest=json.loads((r/'packet-manifest.json').read_text())
for p,v in manifest.items():
 assert hashfile(r/p)==v
 assert hashfile(r/'fresh-extracted'/p)==v
rec=json.loads((r/'fresh-extracted/logs/replay.json').read_text())
assert rec['status']=='PASS Part A conditional on FiniteObstruction'
assert all(x['cap_reason'] is None for x in rec['receipts'])
audit=(r/'fresh-extracted/logs/strict-R4Audit.log').read_text()
m=re.findall(r'LOCAL_TOTAL (\d+)',audit)
assert m
counts=collections.Counter(re.findall(r'MODULE some \(([^)]+)\) DECL ',audit))
# Lean renders Option Name as `some Module`, without parentheses on some builds.
if not counts:counts=collections.Counter(re.findall(r'MODULE some (\S+) DECL ',audit))
assert sum(counts.values())==int(m[-1]),(counts,m)
newmods=['AdmissibleCounting','AdmissibleDiagonal','EndpointOfFinite','SmallOrbitCases','R4Audit']
result={'365943':{'status':'Part A complete; Part B and root acceptance not asserted','endpoints':[{'name':'Nut8.endpoint_of_finite','exact_statement':'(h : Nut8.FiniteObstruction) : Nut8.Target','additional_hypotheses':[]},{'name':'Nut8.coordinate_signedQuotient_admissible','conclusion':'Admissible (signedQuotient m (coordinateGraph G L) ε) ε (ε ^ (m / 2))','hypotheses':'Nut G, Cubic G, actual coordinate equivalence L, translation invariance, periodic integral sign ε, full actual real kernel vector with character formula'}],'target_definition':'∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj], ¬ (Cubic G ∧ Nut G ∧ Circulant 8 G)','unconditional_target_proved':False,'finite_obstruction_proved_here':False,'part_a_gaps':[],'declaration_counts':{'all_local_including_generated':int(m[-1]),'by_module':dict(counts),'new_modules_including_generated':sum(counts[x] for x in newmods)},'validation':'fresh source-only strict replay, leanchecker for every module, complete declaration audit, six negative controls PASS','allowed_axioms':['propext','Classical.choice','Quot.sound'],'input_hashes_unchanged':True,'inherited_modules_byte_identical':True,'root_accepted':False,'credit':0,'campaign_count':'20/40 beyond 39'}}
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(r/'replay-receipts.json').write_text(json.dumps({'status':rec['status'],'receipt':'fresh-extracted/logs/replay.json','audit':'fresh-extracted/logs/strict-R4Audit.log','all_local_declarations':int(m[-1]),'calls':len(rec['receipts']),'peak_private_bytes':max(x['peak_private_bytes'] for x in rec['receipts']),'max_call_wall_seconds':max(x['wall_seconds'] for x in rec['receipts']),'resource_cap_failures':0,'negative_controls':6,'receipts':rec['receipts']},indent=2)+'\n')
files=list((r/'formal').glob('*.lean'))+[r/x for x in ['replay.py','scripts/run_capped.py','SUMMARY.md','GAPS.md','REPRODUCE.md','statement-correspondence.md','results.json','replay-receipts.json','inputs-before.json','inputs-after.json','packet-manifest.json']]+[r/'inputs/nut-formal-r3a/statement-correspondence.md']
with zipfile.ZipFile(r/'nut-r4a-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,p.relative_to(r))
(r/'nut-r4a-source.zip.sha256').write_text(hashfile(r/'nut-r4a-source.zip')+'  nut-r4a-source.zip\n')
print(json.dumps({'declarations':int(m[-1]),'new':sum(counts[x] for x in newmods),'counts':counts,'packet_sha256':hashfile(r/'nut-r4a-source.zip')}))
